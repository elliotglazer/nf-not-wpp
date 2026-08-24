#!/usr/bin/env python3
"""Emit structural recanonicalization certificates for representative trees."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import sys


HERE = Path(__file__).resolve().parent
COMPILER = HERE.parents[1] / "compiler"
sys.path.insert(0, str(COMPILER))

from mm_parser import MMError  # noqa: E402
from syntax import AST  # noqa: E402


OUTPUT = HERE / "GeneratedSmoke.lean"
MANIFEST = HERE / "generated_smoke.json"


def safe(name: str) -> str:
    out = re.sub(r"[^A-Za-z0-9_]", "_", name)
    return "n_" + out if out[:1].isdigit() else out


def expr(tree: AST) -> str:
    if tree.is_variable:
        return safe(tree.variable_name)
    args = [expr(arg) for arg in tree.args]
    table = {
        ("wbot", 0): ".falsum",
        ("wn", 1): f"(.neg {args[0]})" if len(args) == 1 else "",
        ("wi", 2): f"(.imp {args[0]} {args[1]})" if len(args) == 2 else "",
        ("wal", 2): f"(.all {args[0]} {args[1]})" if len(args) == 2 else "",
        ("weq", 2): f"(.objEq {args[0]} {args[1]})" if len(args) == 2 else "",
        ("wel", 2): f"(.objMem {args[0]} {args[1]})" if len(args) == 2 else "",
        ("wceq", 2): f"(.classEq {args[0]} {args[1]})" if len(args) == 2 else "",
        ("wcel", 2): f"(.classMem {args[0]} {args[1]})" if len(args) == 2 else "",
        ("cv", 1): f"(.cv {args[0]})" if len(args) == 1 else "",
        ("cab", 2): f"(.cab {args[0]} {args[1]})" if len(args) == 2 else "",
    }
    out = table.get((tree.head, len(args)))
    if out:
        return out
    raise MMError(f"unsupported core node {tree.sexpr()}")


class CertificateEmitter:
    """Reusable adapter copied directly into the full replay emitter."""

    def wff(self, left: AST, right: AST, indent: str = "  ") -> list[str]:
        if left == right:
            return [indent + "exact RecanonWff.same _"]
        if left.head == "weq" and right.head == "wceq":
            if self._cv_pair(right) != left.args:
                raise MMError("bad objEq -> classEq recanonicalization")
            return [indent + "exact RecanonWff.objEq_classEq _ _"]
        if left.head == "wceq" and right.head == "weq":
            if self._cv_pair(left) != right.args:
                raise MMError("bad classEq -> objEq recanonicalization")
            return [indent + "exact RecanonWff.classEq_objEq _ _"]
        if left.head == "wel" and right.head == "wcel":
            if self._cv_pair(right) != left.args:
                raise MMError("bad objMem -> classMem recanonicalization")
            return [indent + "exact RecanonWff.objMem_classMem _ _"]
        if left.head == "wcel" and right.head == "wel":
            if self._cv_pair(left) != right.args:
                raise MMError("bad classMem -> objMem recanonicalization")
            return [indent + "exact RecanonWff.classMem_objMem _ _"]
        if left.head != right.head or len(left.args) != len(right.args):
            raise MMError(f"wff shape mismatch: {left.sexpr()} / {right.sexpr()}")
        if left.head == "wn":
            return [indent + "apply RecanonWff.neg"] + self.wff(
                left.args[0], right.args[0], indent
            )
        if left.head == "wi":
            return [
                indent + "apply RecanonWff.imp",
                indent + "·",
                *self.wff(left.args[0], right.args[0], indent + "  "),
                indent + "·",
                *self.wff(left.args[1], right.args[1], indent + "  "),
            ]
        if left.head == "wal":
            if left.args[0] != right.args[0]:
                raise MMError("recanonicalization changed a binder")
            return [indent + "apply RecanonWff.all"] + self.wff(
                left.args[1], right.args[1], indent
            )
        if left.head == "wceq":
            return [
                indent + "apply RecanonWff.classEq",
                indent + "·",
                *self.cls(left.args[0], right.args[0], indent + "  "),
                indent + "·",
                *self.cls(left.args[1], right.args[1], indent + "  "),
            ]
        if left.head == "wcel":
            return [
                indent + "apply RecanonWff.classMem",
                indent + "·",
                *self.cls(left.args[0], right.args[0], indent + "  "),
                indent + "·",
                *self.cls(left.args[1], right.args[1], indent + "  "),
            ]
        raise MMError(f"unhandled wff head {left.head}")

    def cls(self, left: AST, right: AST, indent: str = "  ") -> list[str]:
        if left == right:
            return [indent + "exact RecanonClass.same _"]
        if left.head != right.head or len(left.args) != len(right.args):
            raise MMError(f"class shape mismatch: {left.sexpr()} / {right.sexpr()}")
        if left.head == "cab":
            if left.args[0] != right.args[0]:
                raise MMError("recanonicalization changed a class binder")
            return [indent + "apply RecanonClass.cab"] + self.wff(
                left.args[1], right.args[1], indent
            )
        raise MMError(f"unhandled class head {left.head}")

    @staticmethod
    def _cv_pair(tree: AST) -> tuple[AST, AST] | None:
        if len(tree.args) != 2:
            return None
        left, right = tree.args
        if left.head != "cv" or right.head != "cv":
            return None
        return left.args[0], right.args[0]


def v(sort: str, name: str) -> AST:
    return AST.variable(sort, name)


def cv(x: AST) -> AST:
    return AST("class", "cv", (x,))


def main() -> None:
    x, y, z = (v("setvar", name) for name in ("x", "y", "z"))
    eq_left = AST("wff", "weq", (x, y))
    eq_right = AST("wff", "wceq", (cv(x), cv(y)))
    mem_left = AST("wff", "wel", (x, y))
    mem_right = AST("wff", "wcel", (cv(x), cv(y)))

    nested_left_body = AST(
        "wff", "wi", (AST("wff", "wel", (z, x)), eq_left)
    )
    nested_right_body = AST(
        "wff", "wi", (AST("wff", "wcel", (cv(z), cv(x))), eq_right)
    )
    nested_left = AST(
        "wff", "wi",
        (
            AST("wff", "wal", (z, nested_left_body)),
            AST("wff", "wceq", (
                AST("class", "cab", (z, nested_left_body)), cv(y)
            )),
        ),
    )
    nested_right = AST(
        "wff", "wi",
        (
            AST("wff", "wal", (z, nested_right_body)),
            AST("wff", "wceq", (
                AST("class", "cab", (z, nested_right_body)), cv(y)
            )),
        ),
    )
    emitter = CertificateEmitter()
    cert_eq = emitter.wff(eq_left, eq_right)
    cert_mem = emitter.wff(mem_left, mem_right)
    cert_nested = emitter.wff(nested_left, nested_right)

    lines = [
        "import Recanonicalization",
        "",
        "namespace NFChoice.CompactReplayDesign.Recanonicalization.GeneratedSmoke",
        "",
        "open scoped Fol",
        "open NFChoice.Foundation",
        "open NFChoice.Foundation.ExactLiteralTrial",
        "open NFChoice.SemanticCore",
        "open NFChoice.ReplaySupport",
        "",
        "theorem cert_eq (x y : Var) :",
        f"    RecanonWff {expr(eq_left)} {expr(eq_right)} := by",
        *cert_eq,
        "",
        "theorem cert_mem (x y : Var) :",
        f"    RecanonWff {expr(mem_left)} {expr(mem_right)} := by",
        *cert_mem,
        "",
        "theorem cert_nested (x y z : Var) :",
        f"    RecanonWff {expr(nested_left)} {expr(nested_right)} := by",
        *cert_nested,
        "",
        "theorem equality_holds_iff {S : Fol.Structure LNF}",
        "    (hExt : Extensional S) (v : Var -> S) (x y : Var) :",
        f"    Wff.Holds S v {expr(eq_left)} <-> Wff.Holds S v {expr(eq_right)} :=",
        "  (cert_eq x y).holds_iff hExt v",
        "",
        "theorem membership_holds_iff {S : Fol.Structure LNF}",
        "    (hExt : Extensional S) (v : Var -> S) (x y : Var) :",
        f"    Wff.Holds S v {expr(mem_left)} <-> Wff.Holds S v {expr(mem_right)} :=",
        "  (cert_mem x y).holds_iff hExt v",
        "",
        "theorem nested_valid_transport {S : Fol.Structure LNF}",
        "    (hNF : Fol.all_realize_sentence S LiteralHailperinNF)",
        "    (x y z : Var)",
        f"    (h : Wff.Valid S {expr(nested_left)}) :",
        f"    Wff.Valid S {expr(nested_right)} :=",
        "  RecanonWff.valid_mpr (extensional_of_literal_model hNF)",
        "    (cert_nested x y z) h",
        "",
        "#print axioms equality_holds_iff",
        "#print axioms membership_holds_iff",
        "#print axioms nested_valid_transport",
        "",
        "end NFChoice.CompactReplayDesign.Recanonicalization.GeneratedSmoke",
    ]
    text = "\n".join(lines) + "\n"
    OUTPUT.write_text(text, encoding="utf-8", newline="\n")
    MANIFEST.write_text(
        json.dumps(
            {
                "status": "GENERATED_UNCHECKED",
                "equality_certificate_lines": len(cert_eq),
                "membership_certificate_lines": len(cert_mem),
                "nested_certificate_lines": len(cert_nested),
                "nested_left": nested_left.sexpr(),
                "nested_right": nested_right.sexpr(),
                "output_sha256": hashlib.sha256(text.encode()).hexdigest().upper(),
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
        newline="\n",
    )


if __name__ == "__main__":
    main()
