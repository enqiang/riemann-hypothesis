#!/usr/bin/env python3
"""Exercise cache staging, acceptance and activation without Lean or network access."""
from concurrent.futures import ThreadPoolExecutor
import gzip
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
from threading import Lock
import unittest
from unittest.mock import patch


SCRIPT = Path(__file__).resolve().parents[1] / "publish-ci-cache.py"
spec = importlib.util.spec_from_file_location("publish_ci_cache", SCRIPT)
publisher = importlib.util.module_from_spec(spec)
spec.loader.exec_module(publisher)
cache = publisher.cli


def json_lines(*rows):
    return ("\n".join(json.dumps(row) for row in rows) + "\n").encode()


class Publication(unittest.TestCase):
    def setUp(self):
        work = Path(self.enterContext(tempfile.TemporaryDirectory())).resolve()
        self.root = work / "project"
        self.root.mkdir()
        self.work = work
        publisher.git(self.root, "init", "-q")
        (self.root / "src").mkdir()
        (self.root / "src/A.lean").write_text("-- A\n")
        (self.root / "lakefile.toml").write_text('name = "T"\nsrcDir = "src"\n')
        (self.root / "lake-manifest.json").write_text("{}\n")
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v4.37.0-rc1\n")
        publisher.git(self.root, "add", ".")
        self.head = self.commit("build inputs")
        self.identity = cache.identity_at(self.root, self.head, {})
        self.lookup_key = f"{cache.PREFIX}/inputs/{cache.fingerprint(self.identity)}.json"
        self.objects = {}
        self.store_lock = Lock()
        self.enterContext(patch.object(publisher, "log"))
        self.enterContext(patch.object(cache, "fetch", self.fetch))
        self.enterContext(patch.object(publisher, "toolchain_prefix"))
        self.enterContext(patch.object(publisher, "lake_hashes", side_effect=self.lake_hashes))
        self.enterContext(patch.object(publisher, "extraction_error", return_value=None))

        publication = self

        class InMemoryR2(publisher.R2):
            def __init__(self, temporary):
                pass

            def _curl(self, args, body=None):
                key = args[-1].removeprefix(publisher.S3)
                with publication.store_lock:
                    if body is None:
                        if key in publication.objects:
                            return 200, publication.objects[key]
                        return 404, b""
                    publication.assertIn("If-None-Match: *", args)
                    if key in publication.objects:
                        return 412, b""
                    publication.objects[key] = body
                    return 200, b""

        self.r2 = self.enterContext(patch.object(publisher, "R2", side_effect=InMemoryR2))

    def commit(self, message):
        publisher.git(self.root, "-c", "user.name=Test", "-c", "user.email=test@example.com",
                      "commit", "-q", "--allow-empty", "-m", message)
        return publisher.git(self.root, "rev-parse", "HEAD")

    def fetch(self, key, maximum):
        return self.objects.get(key)

    @staticmethod
    def lake_hashes(prefix, paths, work):
        return {str(path): cache.digest(path.read_bytes())[:16] for path in paths}

    def staging(self, name, *, sha=None):
        identity = cache.identity_at(self.root, sha or self.head, {})
        staging = self.work / name
        (staging / "artifacts").mkdir(parents=True)
        payload = name.encode()
        artifact = cache.digest(payload)[:16] + ".ltar"
        (staging / "artifacts" / artifact).write_bytes(payload)
        input_hash = "0" * 16
        contents = json_lines(cache.SCHEMA, [input_hash, artifact])
        header = {"schema": 1, **identity, "input_fingerprint": cache.fingerprint(identity),
                  "map_sha256": cache.digest(contents), "modules": 1}
        manifest = gzip.compress(json_lines(header, ["A", input_hash, artifact, cache.digest(payload)]), mtime=0)
        (staging / "outputs.jsonl").write_bytes(contents)
        (staging / "modules.jsonl.gz").write_bytes(manifest)
        return staging

    def publish_command(self, sha, *arguments):
        with patch.object(sys, "argv", [str(SCRIPT), "--project", str(self.root), "--sha", sha, *arguments]):
            publisher.main()

    def stage(self, name, *, sha=None):
        sha = sha or self.head
        receipt = self.work / f"{name}.json"
        self.publish_command(sha, "--staging", str(self.staging(name, sha=sha)), "--stage-receipt", str(receipt))
        return receipt

    def accept(self, receipt):
        """Use the real candidate CLI and substitute the final build check."""
        def restore(root, directory, record, identity, workers, baseline=None):
            self.assertIsNone(baseline)
            _, _, modules = cache.validated_blobs(record, identity, self.fetch)
            self.assertEqual(len(modules), 1)
            _, _, artifact = modules[0]
            if self.fetch(publisher.ARTIFACT_PREFIX + artifact[:16] + ".art", 1024) == b"rejected":
                raise ValueError("clean build check failed")

        with patch.object(cache, "consume", side_effect=restore), patch.object(
                cache, "find_record", side_effect=AssertionError("candidate restore used ordinary lookup")), patch.object(
                sys, "argv", ["ci-cache-get.py", "--project", str(self.root), "--candidate", str(receipt)]):
            self.assertEqual(cache.main(), 0)

    def test_staging_does_not_activate_and_accepted_retry_can_publish(self):
        rejected = self.stage("rejected")
        self.assertEqual(len(self.objects), 3)
        self.assertIsNone(cache.find_record(self.identity, self.fetch))
        with self.assertRaisesRegex(ValueError, "clean build check failed"):
            self.accept(rejected)
        self.assertIsNone(cache.find_record(self.identity, self.fetch))

        accepted = self.stage("accepted")
        self.accept(accepted)
        self.assertIsNone(cache.find_record(self.identity, self.fetch))
        self.publish_command(self.head, "--activate", str(accepted))
        self.assertEqual(self.objects[self.lookup_key], accepted.read_bytes())
        self.assertEqual(cache.find_record(self.identity, self.fetch), cache.decode(accepted.read_bytes()))

    def test_concurrent_equivalent_candidates_keep_first_writer(self):
        other_head = self.commit("same inputs")
        first = self.stage("first")
        second = self.stage("second", sha=other_head)
        self.accept(first)
        self.accept(second)

        with ThreadPoolExecutor(max_workers=2) as executor:
            first_job = executor.submit(publisher.activate, self.root, self.head, first)
            second_job = executor.submit(publisher.activate, self.root, other_head, second)
            first_job.result()
            second_job.result()
        winner = self.objects[self.lookup_key]
        self.assertIn(winner, (first.read_bytes(), second.read_bytes()))
        publisher.activate(self.root, self.head, first)
        publisher.activate(self.root, other_head, second)
        self.assertEqual(self.objects[self.lookup_key], winner)

    def test_candidate_rejects_wrong_inputs_and_wrong_commit(self):
        receipt = self.stage("original")
        self.r2.reset_mock()
        equivalent = self.commit("same build inputs")
        with self.assertRaisesRegex(ValueError, "not for the selected commit"):
            self.publish_command(equivalent, "--activate", str(receipt))

        (self.root / "src/A.lean").write_text("-- Different build inputs\n")
        publisher.git(self.root, "add", "src/A.lean")
        changed = self.commit("different inputs")
        with self.assertRaisesRegex(ValueError, "does not match the current build inputs"):
            self.publish_command(changed, "--activate", str(receipt))
        with self.assertRaisesRegex(ValueError, "does not match the current build inputs"):
            self.accept(receipt)

        self.r2.assert_not_called()
        self.assertIsNone(cache.find_record(self.identity, self.fetch))

    def test_verify_only_checks_staging_without_opening_r2(self):
        staging = self.staging("verify-only")
        self.publish_command(self.head, "--staging", str(staging))
        artifact, = (staging / "artifacts").iterdir()
        artifact.write_bytes(b"corrupted")
        with self.assertRaisesRegex(ValueError, "does not have the manifest's SHA-256"):
            self.publish_command(self.head, "--staging", str(staging))
        self.r2.assert_not_called()
        self.assertEqual(self.objects, {})


if __name__ == "__main__":
    unittest.main()
