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


class TestR2:
    def __init__(self, temporary):
        assert not os.getenv("R2_ACCOUNT_TOKEN")

    def get(self, key):
        assert key.startswith(f"{cli.PREFIX}/inputs/"), key
        return cli.fetch(key, cli.MAX_RECEIPT)

    def immutable(self, *args):
        raise AssertionError("staging must reuse the active public receipt")

    def create(self, key, data, content_type, cache_control):
        assert self.get(key) is not None, "the input must already be active"
        return False


publisher.R2 = TestR2
publisher.main()
