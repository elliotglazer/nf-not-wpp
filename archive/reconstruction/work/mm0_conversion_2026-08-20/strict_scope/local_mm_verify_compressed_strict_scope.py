#!/usr/bin/env python3
"""Local Metamath verifier with strict active-hypothesis scope checking.

This is an isolated, hardened copy of
``work/formalization_continue/root_integration/local_mm_verify_compressed.py``.
The original verifier is intentionally not imported or modified.

In Metamath, a proof may reference a ``$f`` or ``$e`` label only while that
hypothesis is active.  Assertions remain globally available.  This verifier
checks that rule for every token in a normal proof and for every label in a
compressed proof's parenthesized label list.  It also repeats the check while
executing proof steps as a defense in depth measure.

When inactive hypotheses are found, all such incidents are collected so the
JSON result is useful as a repair inventory.  A theorem containing any such
incident is rejected and is not executed.  Consequently, a failing run is an
audit, not a complete mathematical verification of statements following the
first rejected theorem.
"""

from __future__ import annotations

from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import sys
import traceback


TOK = re.compile(r"\$\(|\$\)|\$\{|\$\}|\$\[|\$\]|\$[cvfedap=.]|\S+")
BASE_NAMES = {
    "52d068cf-64af-4c1e-b9d4-3c54ebc0df12.mm",
    "56475e8c-864a-4be6-ac39-47cb5e00b514.mm",
    "nf.mm",
}
ORIGINAL_VERIFIER_RELATIVE = Path(
    "work/formalization_continue/root_integration/local_mm_verify_compressed.py"
)
EXPECTED_ORIGINAL_SHA256 = (
    "4E0B837A73B736F6B6698840FDCA66057C01489CD09956ABA4573175D73E21D8"
)


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


class InactiveHypothesisError(ValueError):
    """Raised if execution reaches an inactive ``$f`` or ``$e`` label."""


class Assertion:
    def __init__(self, label, expr, hyps, dv, kind, file):
        self.label = label
        self.expr = tuple(expr)
        self.hyps = list(hyps)
        self.dv = set(dv)
        self.kind = kind
        self.file = file


class MM:
    def __init__(self, rootdir):
        self.rootdir = Path(rootdir)
        self.const = set()
        self.vars = set()
        self.labels = {}
        self.scopes = []
        self.seen_files = set()
        self.verified = []
        self.trusted = []
        self.errors = []
        self.scope_errors = []
        self.rejected_proofs = []
        self.proofs_seen = 0
        self.statements_seen = 0
        self.push_scope()

    def push_scope(self):
        if self.scopes:
            parent = self.scopes[-1]
            self.scopes.append(
                {
                    "f": list(parent["f"]),
                    "e": list(parent["e"]),
                    "d": set(parent["d"]),
                }
            )
        else:
            self.scopes.append({"f": [], "e": [], "d": set()})

    def pop_scope(self):
        self.scopes.pop()

    @property
    def sc(self):
        return self.scopes[-1]

    def active_hypothesis_labels(self):
        return {label for label, _ in self.sc["f"] + self.sc["e"]}

    def tokenize(self, path):
        source = path.read_text(errors="replace")
        raw_tokens = TOK.findall(source)
        out = []
        index = 0
        while index < len(raw_tokens):
            if raw_tokens[index] == "$(":
                index += 1
                while index < len(raw_tokens) and raw_tokens[index] != "$)":
                    index += 1
                index += 1
                continue
            out.append(raw_tokens[index])
            index += 1
        return out

    def resolve(self, name, parent):
        candidate = parent / name
        if candidate.exists():
            return candidate
        candidate = self.rootdir / name
        if candidate.exists():
            return candidate
        hits = list(self.rootdir.rglob(name)) + list(Path("/mnt/data").rglob(name))
        return hits[0] if hits else candidate

    def mandatory(self, expr):
        used = {token for token in expr if token in self.vars}
        for _, hypothesis in self.sc["e"]:
            used.update(token for token in hypothesis if token in self.vars)
        floating = [
            (label, hypothesis)
            for label, hypothesis in self.sc["f"]
            if len(hypothesis) >= 2 and hypothesis[1] in used
        ]
        return floating + list(self.sc["e"])

    def add_assertion(self, label, kind, expr, file):
        hyps = self.mandatory(expr)
        used = set()
        for _, hypothesis in hyps:
            used.update(token for token in hypothesis if token in self.vars)
        used.update(token for token in expr if token in self.vars)
        dv = {
            (left, right) if left < right else (right, left)
            for left, right in self.sc["d"]
            if left in used and right in used
        }
        assertion = Assertion(label, expr, hyps, dv, kind, str(file))
        self.labels[label] = assertion
        return assertion

    def subst_expr(self, expr, substitution):
        out = []
        for token in expr:
            out.extend(substitution.get(token, (token,)))
        return tuple(out)

    def decode_compressed_steps(self, assertion, proof):
        try:
            close = proof.index(")")
        except ValueError as exc:
            raise ValueError("unterminated compressed label list") from exc
        refs = [label for label, _ in assertion.hyps] + proof[1:close]
        steps = []
        accumulator = 0
        for char in "".join(proof[close + 1 :]):
            if "U" <= char <= "Y":
                accumulator = accumulator * 5 + (ord(char) - ord("U") + 1)
            elif "A" <= char <= "T":
                number = accumulator * 20 + (ord(char) - ord("A") + 1)
                accumulator = 0
                if number <= len(refs):
                    steps.append(("label", refs[number - 1]))
                else:
                    steps.append(("saved", number - len(refs) - 1))
            elif char == "Z":
                if accumulator:
                    raise ValueError("unfinished compressed number before Z")
                steps.append(("save", None))
            elif char == "?":
                raise ValueError("unknown compressed proof step")
            else:
                raise ValueError(f"invalid compressed proof character {char!r}")
        if accumulator:
            raise ValueError("unfinished compressed proof number")
        return close, refs, steps

    def scope_incident(
        self,
        theorem,
        label,
        proof_encoding,
        location,
        position,
        executed_count,
    ):
        referenced = self.labels.get(label)
        if referenced is None or referenced.kind not in ("$f", "$e"):
            return None
        active_labels = self.active_hypothesis_labels()
        if label in active_labels:
            return None
        active_equivalents = []
        for active_label, active_expr in self.sc["f"] + self.sc["e"]:
            active = self.labels[active_label]
            if active.kind == referenced.kind and tuple(active_expr) == referenced.expr:
                active_equivalents.append(active_label)
        return {
            "theorem": theorem.label,
            "theorem_file": theorem.file,
            "proof_encoding": proof_encoding,
            "location": location,
            "position_1_based": position,
            "referenced_label": label,
            "referenced_kind": referenced.kind,
            "referenced_expression": list(referenced.expr),
            "referenced_file": referenced.file,
            "executed_count": executed_count,
            "active_same_kind_and_expression": active_equivalents,
        }

    def validate_proof_scope(self, assertion, proof):
        """Return every inactive-hypothesis reference in one proof."""
        if not proof:
            raise ValueError("empty proof")
        incidents = []
        if proof[0] == "(":
            close, _, steps = self.decode_compressed_steps(assertion, proof)
            executed = Counter(
                value for kind, value in steps if kind == "label" and value is not None
            )
            # Mandatory hypotheses are active by construction, but checking
            # them makes that invariant explicit and catches future regressions.
            for position, (label, _) in enumerate(assertion.hyps, start=1):
                incident = self.scope_incident(
                    assertion,
                    label,
                    "compressed",
                    "implicit_mandatory_hypothesis",
                    position,
                    executed[label],
                )
                if incident:
                    incidents.append(incident)
            for position, label in enumerate(proof[1:close], start=1):
                incident = self.scope_incident(
                    assertion,
                    label,
                    "compressed",
                    "parenthesized_label_list",
                    position,
                    executed[label],
                )
                if incident:
                    incidents.append(incident)
        else:
            executed = Counter(proof)
            for position, label in enumerate(proof, start=1):
                incident = self.scope_incident(
                    assertion,
                    label,
                    "normal",
                    "proof_step",
                    position,
                    executed[label],
                )
                if incident:
                    incidents.append(incident)
        return incidents

    def require_active_hypothesis(self, label, active_labels, theorem):
        referenced = self.labels[label]
        if referenced.kind in ("$f", "$e") and label not in active_labels:
            raise InactiveHypothesisError(
                f"{theorem}: proof executes inactive {referenced.kind} label {label}"
            )

    def verify_proof(self, assertion, proof, current_d, active_labels):
        if not proof:
            raise ValueError("empty proof")
        if proof[0] == "(":
            _, _, steps = self.decode_compressed_steps(assertion, proof)
        else:
            steps = [("label", token) for token in proof]
        stack = []
        saved = []
        for kind, value in steps:
            if kind == "save":
                if not stack:
                    raise ValueError("save on empty proof stack")
                saved.append(stack[-1])
                continue
            if kind == "saved":
                if value < 0 or value >= len(saved):
                    raise ValueError(f"bad saved-step reference {value}")
                stack.append(saved[value])
                continue
            token = value
            if token not in self.labels:
                raise KeyError(f"unknown proof label {token}")
            self.require_active_hypothesis(token, active_labels, assertion.label)
            referenced = self.labels[token]
            if referenced.kind in ("$f", "$e"):
                stack.append(referenced.expr)
                continue
            hypothesis_count = len(referenced.hyps)
            if len(stack) < hypothesis_count:
                raise ValueError(f"stack underflow at {token}")
            args = stack[-hypothesis_count:] if hypothesis_count else []
            if hypothesis_count:
                del stack[-hypothesis_count:]
            substitution = {}
            for (_, hypothesis), got in zip(referenced.hyps, args):
                if (
                    hypothesis
                    and hypothesis[0] in ("class", "wff", "setvar")
                    and len(hypothesis) == 2
                    and hypothesis[1] in self.vars
                ):
                    if not got or got[0] != hypothesis[0]:
                        raise ValueError(
                            f"type mismatch at {token}: {hypothesis} vs {got}"
                        )
                    variable = hypothesis[1]
                    value = tuple(got[1:])
                    if variable in substitution and substitution[variable] != value:
                        raise ValueError("inconsistent subst")
                    substitution[variable] = value
            for (_, hypothesis), got in zip(referenced.hyps, args):
                want = self.subst_expr(hypothesis, substitution)
                if tuple(got) != want:
                    raise ValueError(
                        f"hyp mismatch at {token}: want {want}, got {got}"
                    )
            for left, right in referenced.dv:
                sub_left = {
                    token
                    for token in substitution.get(left, (left,))
                    if token in self.vars
                }
                sub_right = {
                    token
                    for token in substitution.get(right, (right,))
                    if token in self.vars
                }
                for first in sub_left:
                    for second in sub_right:
                        if first == second:
                            raise ValueError(
                                f"DV collapse at {token}: {left},{right}->{first}"
                            )
                        pair = (
                            (first, second) if first < second else (second, first)
                        )
                        if pair not in current_d:
                            raise ValueError(f"missing DV {pair} applying {token}")
            stack.append(self.subst_expr(referenced.expr, substitution))
        if len(stack) != 1:
            raise ValueError(f"final stack size {len(stack)}")
        if stack[0] != assertion.expr:
            raise ValueError(f"wrong conclusion: {stack[0]} != {assertion.expr}")

    def process(self, path, trust=None):
        path = Path(path).resolve()
        if path in self.seen_files:
            return
        self.seen_files.add(path)
        is_base = path.name in BASE_NAMES or trust is True
        tokens = self.tokenize(path)
        index = 0
        while index < len(tokens):
            token = tokens[index]
            if token == "$[":
                name = tokens[index + 1]
                assert tokens[index + 2] == "$]"
                index += 3
                included = self.resolve(name, path.parent)
                self.process(included, trust=(included.name in BASE_NAMES))
                continue
            if token == "${":
                self.push_scope()
                index += 1
                continue
            if token == "$}":
                self.pop_scope()
                index += 1
                continue
            if token in ("$c", "$v", "$d"):
                kind = token
                index += 1
                values = []
                while tokens[index] != "$.":
                    values.append(tokens[index])
                    index += 1
                index += 1
                self.statements_seen += 1
                if kind == "$c":
                    self.const.update(values)
                elif kind == "$v":
                    self.vars.update(values)
                else:
                    for left_index in range(len(values)):
                        for right_index in range(left_index + 1, len(values)):
                            left, right = values[left_index], values[right_index]
                            self.sc["d"].add(
                                (left, right) if left < right else (right, left)
                            )
                continue
            if index + 1 < len(tokens) and tokens[index + 1] in (
                "$f",
                "$e",
                "$a",
                "$p",
            ):
                label = token
                kind = tokens[index + 1]
                index += 2
                expr = []
                while tokens[index] not in ("$=", "$."):
                    expr.append(tokens[index])
                    index += 1
                proof = []
                if tokens[index] == "$=":
                    index += 1
                    while tokens[index] != "$.":
                        proof.append(tokens[index])
                        index += 1
                index += 1
                self.statements_seen += 1
                if kind == "$f":
                    assertion = Assertion(label, expr, [], set(), kind, str(path))
                    self.labels[label] = assertion
                    self.sc["f"].append((label, tuple(expr)))
                    continue
                if kind == "$e":
                    assertion = Assertion(label, expr, [], set(), kind, str(path))
                    self.labels[label] = assertion
                    self.sc["e"].append((label, tuple(expr)))
                    continue
                assertion = self.add_assertion(label, kind, expr, path)
                if kind == "$p":
                    self.proofs_seen += 1
                    incidents = self.validate_proof_scope(assertion, proof)
                    if incidents:
                        self.scope_errors.extend(incidents)
                        self.rejected_proofs.append(label)
                    elif is_base:
                        self.trusted.append(label)
                    else:
                        self.verify_proof(
                            assertion,
                            proof,
                            set(self.sc["d"]),
                            self.active_hypothesis_labels(),
                        )
                        self.verified.append(label)
                continue
            index += 1


def main():
    if len(sys.argv) < 2:
        print(
            "usage: local_mm_verify_compressed_strict_scope.py root.mm [json]"
        )
        return 2
    root = Path(sys.argv[1]).resolve()
    output = (
        Path(sys.argv[2]).resolve()
        if len(sys.argv) > 2
        else root.with_suffix(".strict_scope.verify.json")
    )
    workspace = Path(__file__).resolve().parents[3]
    original_verifier = workspace / ORIGINAL_VERIFIER_RELATIVE
    original_sha256 = (
        sha256_file(original_verifier) if original_verifier.exists() else None
    )
    verifier = MM(root.parent)
    record = {
        "schema": "strict-metamath-scope-verification-v1",
        "root": str(root),
        "root_bytes": root.stat().st_size if root.exists() else None,
        "root_sha256": sha256_file(root) if root.exists() else None,
        "strict_verifier": str(Path(__file__).resolve()),
        "strict_verifier_sha256": sha256_file(Path(__file__).resolve()),
        "source_verifier": str(original_verifier),
        "source_verifier_expected_sha256": EXPECTED_ORIGINAL_SHA256,
        "source_verifier_actual_sha256": original_sha256,
        "source_verifier_unchanged": original_sha256 == EXPECTED_ORIGINAL_SHA256,
        "ok": False,
        "status": "ERROR",
    }
    try:
        verifier.process(root)
        scope_ok = not verifier.scope_errors
        record.update(
            ok=scope_ok,
            status="PASS" if scope_ok else "FAIL_INACTIVE_HYPOTHESIS_SCOPE",
            statements_seen=verifier.statements_seen,
            proofs_seen=verifier.proofs_seen,
            verified_scope_clean_proofs=len(verifier.verified),
            trusted_scope_clean_proofs=len(verifier.trusted),
            rejected_proof_count=len(verifier.rejected_proofs),
            rejected_proofs=verifier.rejected_proofs,
            inactive_hypothesis_reference_count=len(verifier.scope_errors),
            inactive_hypothesis_references=verifier.scope_errors,
            mathematical_verification_complete=scope_ok,
            audit_caveat=(
                None
                if scope_ok
                else "Rejected proofs were not executed; later clean proofs were checked "
                "using their assertions, so this failing run is a complete scope audit "
                "but not a complete mathematical verification."
            ),
            last_verified=verifier.verified[-20:],
        )
    except Exception as exc:
        record.update(
            error=repr(exc),
            traceback=traceback.format_exc(),
            statements_seen=verifier.statements_seen,
            proofs_seen=verifier.proofs_seen,
            verified_scope_clean_proofs=len(verifier.verified),
            rejected_proof_count=len(verifier.rejected_proofs),
            rejected_proofs=verifier.rejected_proofs,
            inactive_hypothesis_reference_count=len(verifier.scope_errors),
            inactive_hypothesis_references=verifier.scope_errors,
            mathematical_verification_complete=False,
            last_verified=verifier.verified[-20:],
        )
    output.write_text(
        json.dumps(record, indent=2) + "\n", encoding="utf-8", newline="\n"
    )
    print(json.dumps(record))
    return 0 if record["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
