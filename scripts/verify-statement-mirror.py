#!/usr/bin/env python3
"""Reject drift between Palomar's self-contained Challenge and Solution surface."""

from __future__ import annotations

from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parent.parent
EXPECTED_SURFACE_IMPORTS = [
    "import Mathlib.Data.Finset.Basic",
    "import Mathlib.Data.Finset.Lattice.Fold",
    "import Mathlib.Data.Set.Basic",
]
EXPECTED_SOLUTION_IMPORTS = [
    "import NFNotWPP.Surface",
    "import NFStandard.NotWPPPrfBridge",
]


def fail(message: str) -> None:
    print(f"statement-mirror: FAIL: {message}", file=sys.stderr)
    raise SystemExit(1)


def read_source(relative: str) -> str:
    data = (ROOT / relative).read_bytes()
    if b"\r" in data:
        fail(f"{relative} must use LF line endings")
    try:
        return data.decode("utf-8")
    except UnicodeDecodeError as error:
        fail(f"{relative} is not UTF-8: {error}")


def imports(source: str) -> list[str]:
    return re.findall(r"^import .+$", source, flags=re.MULTILINE)


def exact_slice(source: str, start_marker: str, end_marker: str, relative: str) -> str:
    try:
        start = source.index(start_marker)
        end = source.index(end_marker, start)
    except ValueError:
        fail(f"could not locate the declaration region in {relative}")
    return source[start:end]


challenge = read_source("Challenge.lean")
surface = read_source("NFNotWPP/Surface.lean")
solution = read_source("Solution.lean")

if imports(challenge) != EXPECTED_SURFACE_IMPORTS:
    fail("Challenge.lean must import exactly the three canonical Mathlib modules")
if imports(surface) != EXPECTED_SURFACE_IMPORTS:
    fail("NFNotWPP/Surface.lean must use exactly Challenge's three Mathlib imports")
if imports(solution) != EXPECTED_SOLUTION_IMPORTS:
    fail("Solution.lean must import the clean Surface before the proof dependency")

challenge_region = exact_slice(
    challenge,
    "namespace NFNotWPP\n",
    "\n/-!\nPALOMAR CHALLENGE:",
    "Challenge.lean",
)
surface_region = exact_slice(
    surface,
    "namespace NFNotWPP\n",
    "\nend NFNotWPP",
    "NFNotWPP/Surface.lean",
)
if challenge_region != surface_region:
    fail("Challenge and solution-side Surface declaration regions differ")

if "theorem NF_proves_not_WPP" in surface:
    fail("the solution-side Surface must not contain the headline theorem")
if "NFStandard.NotWPPPrfBridge" in surface:
    fail("the solution-side Surface must remain independent of the proof development")

headline_start = "theorem NF_proves_not_WPP :"
headline_end = ":= by"
challenge_headline = exact_slice(
    challenge, headline_start, headline_end, "Challenge.lean"
)
solution_headline = exact_slice(
    solution, headline_start, headline_end, "Solution.lean"
)
if challenge_headline != solution_headline:
    fail("Challenge and Solution headline theorem types differ")

print(
    "statement-mirror: PASS: Challenge is self-contained and its declaration "
    "region exactly matches the clean Solution surface"
)
