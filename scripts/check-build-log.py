#!/usr/bin/env python3
"""Reject unexpected info diagnostics from project sources in a Lake build log."""

import re
import sys
from pathlib import Path

SOURCE_INFO = re.compile(r"^info: (?:\./)?src/.+\.lean:[0-9]+:[0-9]+:")
# Remove this exception when #9138 clears the existing tactic suggestion.
KNOWN_INFO = (
    "info: src/New/Spanning/MainTerm/GlobalSieve.lean:294:25: Try this:",
    "  [apply] ring_nf",
)


def main():
    log = Path(sys.argv[1]).read_text(encoding="utf-8").splitlines()
    unexpected = [
        line
        for line, following in zip(log, log[1:] + [""])
        if SOURCE_INFO.match(line) and (line, following) != KNOWN_INFO
    ]
    if not unexpected:
        return 0

    print(*unexpected, sep="\n", file=sys.stderr)
    print(
        "::error::Project modules report unexpected info diagnostics. "
        "Resolve tactic suggestions or guard expected command output with #guard_msgs.",
        file=sys.stderr,
    )
    return 1


if __name__ == "__main__":
    sys.exit(main())
