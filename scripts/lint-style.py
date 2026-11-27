#!/usr/bin/env python3
"""Report new Mathlib text-style diagnostics in Lean files between BASE and HEAD."""
import argparse
from collections import Counter
import json
from pathlib import Path
import subprocess
import tempfile


def git(*args):
    return subprocess.check_output(["git", *args])


def changes(base):
    fields = git("diff", "--name-status", "-z", "--find-renames", "--diff-filter=AMRT",
                 base, "HEAD", "--", "src/").decode().split("\0")
    entries = iter(fields[:-1])
    for status in entries:
        path = next(entries)
        target = next(entries) if status.startswith("R") else path
        if target.endswith(".lean"):
            old = path if status != "A" and path.endswith(".lean") else None
            yield old, target


def lean(mode, *args):
    return ["lake", "env", "lean", "--run", "scripts/LintStyle.lean", mode, *args]


def lint(root, paths):
    if not paths:
        return []
    result = subprocess.run(lean("text", root, *paths), stdout=subprocess.PIPE, text=True)
    if result.returncode:
        raise SystemExit(result.stdout or "Mathlib's text linter failed.")
    return [json.loads(line) for line in result.stdout.splitlines()]


def key(diagnostic, path):
    return path, diagnostic["code"], diagnostic["message"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("base", metavar="BASE")
    args = parser.parse_args()
    base = git("rev-parse", "--verify", "--end-of-options", args.base + "^{commit}").decode().strip()
    changed = list(changes(base))
    if not changed:
        return 0

    old_paths = {}
    new_paths = []
    checked_names = []
    with tempfile.TemporaryDirectory(prefix="grh-lint-style-") as temporary:
        for old, new in changed:
            name = new.removeprefix("src/")
            path = Path(new)
            if path.is_symlink() or not path.is_file():
                raise SystemExit(f"Expected a regular Lean source file: {new}")
            new_paths.append(name)
            if old != new:
                checked_names.append(name)
            if old is not None:
                old_name = old.removeprefix("src/")
                old_paths[old_name] = name
                snapshot = Path(temporary) / old_name
                snapshot.parent.mkdir(parents=True, exist_ok=True)
                snapshot.write_bytes(git("show", f"{base}:{old}"))
        inherited = Counter(key(row, old_paths[row["path"]]) for row in lint(temporary, list(old_paths)))

    failures = 0
    for row in lint("src", new_paths):
        diagnostic = key(row, row["path"])
        if inherited[diagnostic]:
            inherited[diagnostic] -= 1
        else:
            print(f"src/{row['path']}:{row['line']}: {row['message']}")
            failures += 1
    name_errors = checked_names and subprocess.run(lean("names", *checked_names)).returncode
    return int(bool(failures or name_errors))


if __name__ == "__main__":
    raise SystemExit(main())
