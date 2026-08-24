# Nominal WPP final endpoint package v1

This package closes the completed nominal replay with the exact public result

`LiteralHailperinNF ⊢ₛ' Fol.bd_not SourceWPPFOL`.

It does not reinterpret the endpoint.  The generated input theorem must be
exactly

`NFChoice.DirectNominalPrf.WPPReplay.g_wppfiniteblocknotwppndv : Nominal.NPrf (Wff.neg syn_wwpp)`.

The source generator rejects any input unless all of the following hold:

1. the translator resource pins repaired Metamath SHA-256
   `868DF831E63E28AA924CC099510CD9E5D3BE18CD8416A20B335F5BBF3B42ED3F`;
2. its endpoint is `wppfiniteblocknotwppndv`, AST `(wn wwpp)`, at closure
   theorem ordinal 4321;
3. its final umbrella exports `g_wppfiniteblocknotwppndv`;
4. the matching kernel resource records a successful `--trust=0` umbrella
   check and exactly `[propext, Classical.choice, Quot.sound]`;
5. the exact eleven-axiom theory, WPP syntax, closedness proof, lowering
   endpoint, and nominal-to-public bridge retain their pinned hashes.

The output directory is append-only: it must not exist before generation.
Generation runs no Lean process.  The trust-zero runner then compiles the
pinned bridge and the one-theorem wrapper sequentially, checks empty stderr,
and requires the exact three-axiom print for every public theorem checked.

The package is deliberately specialized to the Hailperin NF / WPP profile.
It is reusable for future regenerated versions of this same proof whose final
replay module name changes, because that name is read from the validated final
translator resource rather than hard-coded in the template.
