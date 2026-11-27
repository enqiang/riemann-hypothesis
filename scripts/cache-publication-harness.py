"""Run the production workflow's two writer commands against a disposable substitute for R2."""
import importlib.util
import os
from pathlib import Path
import sys

script = Path(__file__).with_name("publish-ci-cache.py")
spec = importlib.util.spec_from_file_location("publisher", script)
publisher = importlib.util.module_from_spec(spec)
spec.loader.exec_module(publisher)
cli = publisher.cli
root = Path.cwd()
staging = Path(os.environ["RUNNER_TEMP"]) / "staging"

if sys.argv[1:] == ["fixture"]:
    identity = cli.identity_at(root, os.environ["SHA"], {})
    record = cli.find_record(identity)
    assert record is not None, "The target must have a public cache for the test fixture"
    staging.mkdir()
    for name, key in (("outputs.jsonl", "map_key"), ("modules.jsonl.gz", "module_manifest_key")):
        data = cli.fetch(record[key])
        assert data is not None, record[key]
        (staging / name).write_bytes(data)
    sys.exit(0)

published = {}


class TestR2:
    def __init__(self, temporary):
        assert not os.getenv("R2_ACCOUNT_TOKEN")

    def immutable(self, key, body, content_type):
        assert key.startswith((f"{cli.PREFIX}/maps/", f"{cli.PREFIX}/module-manifests/")), key
        assert cli.fetch(key) == body, key
        return "public object verified; test performed no R2 writes"

    def create(self, key, data, content_type, cache_control):
        record = cli.decode(data)
        assert key == f"{cli.PREFIX}/inputs/{record['input_fingerprint']}.json"
        assert record["candidate_head"] == os.environ["SHA"]
        assert not published
        published[key] = data
        return True


publisher.R2 = TestR2
if "--activate" in sys.argv:
    cli.fetch = lambda key, maximum: published.get(key)
publisher.main()
