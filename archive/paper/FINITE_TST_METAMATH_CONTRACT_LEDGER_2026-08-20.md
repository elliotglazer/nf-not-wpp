# Finite-TST manuscript to Metamath contract ledger

Date: 2026-08-20  
Manuscript audited: `output/pdf/NF_Refutes_WPP_Unconditional_Proof.tex`  
Concrete specialization: `X0 = ~P1 ~P1 ~P1 ~P1 ~P1 ~P1 1c`

## Executive verdict

The formalization is complete.  The public no-hypothesis theorem is

```text
wppfiniteblocknotwppndv $p |- -. WPP $.
```

It has no essential hypotheses and no mandatory distinct-variable pairs.
The cumulative checkpoint and its declared-parent rebase both pass the two
independent verifiers with 7973 proofs and 16074 statements.  The frozen
theorem `cfbfixedblocknotwppfrominjndv` reduces the terminal proof to the
single exact WPP-dependent injection

```text
E. f f :
  ~P1 ~P1 ~P1 HNOrd ~P X0 -1-1->
  HNOrd ~P ~P HNOrd X0.
```

The canonical common-ambient graph, its pointwise coverage proof, its image
coverage theorem, and its existential injection wrapper are all frozen.  The
completed integration chain is:

```text
concrete padded-product comparison at X0
  -> pointwise first-difference carrier injection
  -> three-step representative transport / common-ambient range coverage
  -> canonical common-ambient fixed-block graph
  -> existential injection
  -> cfbfixedblocknotwppfrominjndv
  -> -. WPP.
```

The generic Hartogs-product theorem in the manuscript is not required for
this concrete terminal.  A choice-free comparison only at `X0` is sufficient.

## A mandatory notation distinction

The manuscript notation `s^r` is metasyntactic.  It means that finitely many
displayed occurrences have been copied upward under one fixed compatible TST
assignment.  It does **not** denote a global NF set-function.

The Metamath objects are different:

| Manuscript notation | Metamath object | Meaning |
|---|---|---|
| `s^r A` | `~P1^r A` | set-coded carrier of iterated singleton copies |
| raised relation code | `SI^r R` | set-coded singleton image of an ordinary type-level relation graph |
| `theta_A^r` | an iterate of `HNSIQuoMap` | quotient-level support-shift bijection |
| `A x_K B` | `A X._k B` | Kuratowski product; raises two relative types |
| ordinary function/product graph | `A X. B` and QR ordered pairs | type-level graph; no extra carrier depth |

No proof may rewrite manuscript `s^r` directly to `~P1^r` or rewrite a
relation directly to `SI^r R`.  Such a rewrite is valid only after the
relevant support, graph-conjugation, and two-way quotient-coherence theorem
has been invoked.

## Exact final fixed-block graph

For a set `X`, abbreviate

```text
A0 = ~P1 ~P1 ~P1 ~P X
B  = ~P ~P HNOrd X
C  = A0 u. B

Theta =
  ( HNSIQuoMap ~P1 ~P1 ~P X o.
    ( SI HNSIQuoMap ~P1 ~P X o.
      SI SI HNSIQuoMap ~P X ) )

G =
  ( ( `' HNQInc ( B , C ) o.
      ( HNQInc ( A0 , C ) o. Theta ) ) |`
    ~P1 ~P1 ~P1 HNOrd ~P X ).
```

The semantic join proved by `cfbwppfixedblockhnqimagecoverndv` is exactly

```text
WPP ->
  ( ( HNQInc ( A0 , C ) o. Theta ) "
      ~P1 ~P1 ~P1 HNOrd ~P X ) C_
    ran HNQInc ( B , C ).
```

From this theorem:

```text
cfbwppfixedblockhnqgraphinjndv |-
  ( WPP -> G :
      ~P1 ~P1 ~P1 HNOrd ~P X -1-1->
      HNOrd ~P ~P HNOrd X ).
```

The graph term contains no first-difference carrier, padding injection, or
transport witness.  All of those witnesses occur only in the proof of range
coverage.

## Frozen checkpoint inventory

The safest cumulative ancestry is the following.  Later entries already
include earlier entries unless a parent-free suffix is explicitly replayed.

| Order | Checkpoint | SHA-256 | Principal export |
|---:|---|---|---|
| 1 | `cumulative_finite_block/fixed_block_integration_base/fixed_block_integration_base_frozen_checkpoint.mm` | `73D961263B83BCFCB10BFF59C89E0D823DF1822ECBDAE4AE5BC40A02BFC95606` | width-six endpoint plus shared ancestors |
| 2 | `cumulative_finite_block/integration_audit/cfb_base_hncard_normalization_frozen_checkpoint.mm` | `68E2F141B6B59EC3C3EAD10B865442A625ECFD38A2E96826A3B0B8ADCA134FA4` | `cfbsourceledgerndv` |
| 3 | `cumulative_finite_block/common_ambient_hartogs_graph/common_ambient_hartogs_graph_frozen_checkpoint.mm` | `5CF423AF0F69352E67814A53316071EA0BB7C18CC44DE7F46D55CF03726D6783` | `hnpw13quoshiftf1ondv`, `wppfixedblockhnqgraphinjndv` |
| 4 | `cumulative_finite_block/integration_audit/cfb_target_landing_frozen_checkpoint.mm` | `394B6DEE73E6DF1938F8777AD5A222F7A53FF64B00B036090C8D4CE99D840A7D` | target ledger, cancellation, F6 landing |
| 5 | `cumulative_finite_block/integration_audit/cfb_target_terminal_frozen_checkpoint.mm` | `303BD192429EF763BEFB98B6653C9C6E413AA5491573083D0643F23CD6D575E5` | no-witness F6 adapter and final `-. WPP` interface |

The terminal checkpoint was independently accepted by both verifiers with
7935 verified proofs, 15932 statements, and no trusted new assertion.  Its
parent-free suffix is
`cumulative_finite_block/integration_audit/cfb_target_terminal_parent_free_suffix.mm`,
SHA-256
`8630DA7A1CA84AD241CDFFB15970E7D249697B9D0BDBB36E89ADA86DF6C553EA`.

Additional frozen branches must be integrated by their parent-free suffixes,
not by including their full checkpoints after item 5:

| Branch | Frozen checkpoint | SHA-256 | Export |
|---|---|---|---|
| unequal-carrier lowering | `cumulative_finite_block/subset_graph_lowering/subset_graph_lowering_frozen_checkpoint.mm` | `2C1F5AA62667E2C2A8221932194C0991D84E198FCA02714AB8DB2D86A1886C44` | `cfbsubsetlowerndv`, `cfbgraphf1lowerndv` |
| WPP padding/Hartogs bridge | `cumulative_finite_block/typed_padding_hartogs_bridge/typed_padding_hartogs_bridge_frozen_checkpoint.mm` | `7F34EB45C2969929A2D236B9A341005F219613FCF5EB8ED2B31F1E3A903380CB` | `cfbtypedpaddinghnordinjndv` |
| common-ambient product envelope | `cumulative_finite_block/typed_padding_hartogs_bridge/supported_product_envelope_frozen_checkpoint.mm` | `7328EE0D76C02D1E53EB444DE6193C3D803AAB9493BD6BA22D03E24AD5953BD5` | `cfbsupportedproductcoverboundndv` |
| representative code transport | `cumulative_finite_block/typed_padding_hartogs_bridge/product_code_transport_frozen_checkpoint.mm` | `B87AA4C3829FC6B83B35317159A9D55B52F8D95DFC13862B7165C748B2463A66` | `cfbhnqinjcodecoverndv` |
| concrete universal-product absorption | `cumulative_finite_block/typed_padding_hartogs_bridge/concrete_universal_product_absorption/concrete_universal_product_absorption_frozen_checkpoint.mm` | `707DB436F44E6B159D0B4D7CEB58505170B49E891876E5299F541C5DF53B4D5C` | `cfbliteralp16onehncardboundndv` |

The concrete-product parent-free suffix is
`cumulative_finite_block/typed_padding_hartogs_bridge/concrete_universal_product_absorption/concrete_universal_product_absorption_parent_free_suffix.mm`,
SHA-256
`EF9D78ADDE298097A0D894A534204EC8CF9F9B9854E49C7C372B7004973AC305`.
It must be preceded, on the terminal ancestry, by
`cumulative_finite_block/typed_padding_hartogs_bridge/supported_product_residual/threshold_tc2_injection_parent_free_suffix.mm`,
SHA-256
`7F221B860D34EBD44A89D8D741DDD477EB504EE5A66B252A9F5B3F7DBB96908C`;
that suffix supplies `cfbthresholdtc2injndv` and
`cfbthresholdnn2lencndv` without replaying the shared fixed-block base.
The literal terminal replay
`cfb_target_terminal_frozen_checkpoint.mm` + threshold suffix + concrete
product suffix has been accepted independently by both verifiers with 7942
proofs, 15945 statements, and no new trusted assertion.

## Manuscript lemma-by-lemma map

Statuses below distinguish a generic manuscript theorem from the exact
fixed specialization actually needed by the Metamath terminal.

### 1. Basic `T`-calculus (`lem:t-calculus`, lines 138--154)

**Status:** sufficient fixed APIs are frozen; the four-part prose lemma is
not needed as one bundled theorem.

Relevant labels:

```text
tlecg       comparison reflection through one common T_c
tc3lecan    cancellation of three common T_c iterates
tc6lecan    cancellation of six common T_c iterates
tccl        natural-cardinal closure under T_c
tcnc        singleton-cardinality normalization
ncpw1c      Nc(~P 1c) = Nc(1c)
```

Concrete consumers are `cfbfixedblockcancel3ndv`,
`cfbsourceledgerndv`, and `cfbtargetledgerndv`.  The parity, iteration, and
stopped-orbit facts needed at width six are already buried in the frozen
`wppconcrete6notwppfrompointndv` package.

### 2. Supported local lowering (`lem:local-lowering`, lines 195--231)

**Status:** the proof-specific set and unequal-graph lowering interfaces are
frozen; the generic prose schema remains a metatheoretic description.

```text
cfbsubsetlowerndv |-
  ( S C_ ~P1 A -> ( U. S C_ A /\ S = ~P1 U. S ) ).

cfbgraphsupportndv |-
  ( S C_ ( ~P1 A X. ~P1 B ) ->
    { <.x,y>. | {x} S {y} } C_ ( A X. B ) ).

cfbgraphrecoverndv |-
  ( S C_ ( ~P1 A X. ~P1 B ) ->
    SI { <.x,y>. | {x} S {y} } = S ).

cfbgraphf1lowerndv |-
  ( S : ~P1 A -1-1-> ~P1 B ->
    { <.x,y>. | {x} S {y} } : A -1-1-> B ).
```

Function and injection reflection are separately exported as
`cfbmapsireflectimndv`, `cfbmapsireflectndv`,
`cfbf1sireflectimndv`, and `cfbf1sireflectndv`.

For Hartogs quotient support shift, use the actual quotient map, not a
rewrite:

```text
hnsiquomapf1ondv |-
  HNSIQuoMap A : ~P1 HNOrd A -1-1-onto-> HNOrd ~P1 A.

hnpw13quoshiftf1ondv |-
  Theta : ~P1 ~P1 ~P1 HNOrd A -1-1-onto->
          HNOrd ~P1 ~P1 ~P1 A.
```

The threefold theorem supplies both forward naturality and reverse coverage.

### 3. Common-ambient quotient graph (`lem:common-ambient-quotient-graph`, lines 249--269)

**Status:** frozen, both generically and at the exact fixed block.

```text
hnqcommonprecoverinjndv
hnfixedblockhnqcoverinjndv
wppfixedblockhnqgraphinjndv
```

`hnqcommonprecoverinjndv` takes a source alignment injection `J` and a range
coverage premise; `hnfixedblockhnqcoverinjndv` installs `Theta`; the WPP
wrapper merely places WPP in front of the exact coverage hypothesis.

### 4. Typed WPP padding (`lem:typed-wpp-padding`, lines 298--335)

**Status:** the exact consequence needed by the replay is frozen.  It is not
necessary to expose the tagged even/odd graph as the public theorem.

```text
wppsurjcountclndv:
  F : X -onto-> D
  |- WPP -> E. k k : D -1-1-> ( X X. Nn ).

cfbtypedpaddingouterhnboundndv:
  F : (X X._k X) -onto-> ~P1 D
  R We D
  |- WPP -> T_c T_c Nc(~P1 D)
       <_c HNCard(((X X._k X) X. Nn)).

cfbtypedpaddinghnordinjndv:
  [same data plus the special padded-product comparison]
  |- WPP -> E. f f : ~P1 D -1-1-> HNOrd X.
```

The empty `D` case is harmless: the empty injection discharges the local
carrier conclusion, and no padding surjection is required.

### 5. Typed Hartogs product (`lem:typed-hartogs-product`, lines 337--393)

**Status:** the generic product theorem is not frozen and is no longer on the
critical path.  The witness-independent common-ambient packaging is frozen;
the concrete universal-base comparison is the only arithmetic input needed.

Frozen interfaces:

```text
cfbhnqcommoncoverinjndv
cfbhnqcommoncovercardndv
cfbsupportedproductcoverboundndv
cfbhnqinjcodecoverndv
```

The exact concrete comparison consumed downstream is

```text
HNCard
  ( ( ( X0 X._k X0 ) X. Nn ) ) <_c
  T_c T_c HNCard X0.
```

This fixed theorem is frozen by universal-cardinal absorption
(`X0 = ~P1^7 _V`) using `ncvsq`, the honest ordinary-product singleton
equivalence `pw1xpshiftenndv`, and the QR/Kuratowski pairing bridge.  It does
not require a generic least-preimage selector or the manuscript's general
Hartogs-product maximum theorem.  Its consumer-facing no-essential-hypothesis
label is

```text
cfbliteralp16onehncardboundndv:
  HNCard(((~P1^6 1c X._k ~P1^6 1c) X. Nn))
    <_c T_c T_c HNCard(~P1^6 1c).
```

The equality `1c = ~P1 _V` is raised six times inside this theorem, so the
downstream replay requires no predecessor operation and no extra rewrite.

### 6. Supported first-difference envelope (`lem:supported-first-difference-envelope`, lines 395--424)

**Status:** frozen and discharged at the exact concrete padded-product
comparison.

```text
cfbtypedpaddingproductbridgendv
cfbtypedpaddinghnordinjndv
cfbtypedpaddingfromproductcoverinjndv
```

The occurrence-level first-difference specialization currently exported in
the integration work is

```text
cfbfdwppcarrierinjndv:
  R We A
  A C_ ~P X
  HNCard(((X X._k X) X. Nn)) <_c T_c T_c HNCard X
  |-
  WPP -> E. k k :
    ~P1 ~P1 ~P1 A -1-1-> ~P ~P HNOrd X.
```

Its projection-safe consumer is frozen as `cfbwpphwcncarrierinjndv`, and the
subsequent arbitrary-code point theorem is
`cfbhnpw13genericcodepointcoverndv`.

### 7. Countable padding (`lem:padding`, lines 433--450)

**Status:** frozen as `wppsurjcountclndv` in the exact same-type graph form.

The manuscript's untyped notation `U x omega` becomes the QR type-level
product `(U X. Nn)` only after the displayed carriers are at one level.

### 8. Carrier first-difference compression (`lem:first-difference`, lines 452--502)

**Status:** combinatorial core frozen.

```text
fdcolcodetc2le2 |-
  ( (R We A /\ A C_ ~P B) ->
    T_c T_c Nc A <_c Nc ~P ~P FDif(R,A,B) ).

fdpivmap2onto |-
  FDPivMap2(R,A,B) : (B X._k B) -onto-> FDPivRange2(R,A,B).

fdifpw1ssrange2raw |-
  ~P1 FDif(R,A,B) C_ FDPivRange2(R,A,B).

wppfdpivrangencdlitraw |-
  WPP -> Nc FDPivRange2(R,A,B)
    <_c Nc(((B X._k B) X. Nn)).
```

The optional quotient route is also frozen:

```text
lncollapsefog
fdlnquopw2bound
fdlnwtypespw2bound
```

It is not used in the sharp common-ambient replay, because the latter pushes
one representative order directly into `~P^2 HNOrd X`.

### 9. Hartogs products (`lem:products`, lines 504--526)

**Status:** not needed as a generic formal theorem.  Its only critical use in
the manuscript is replaced by the fixed comparison at `X0` displayed under
item 5.  Formalizing the generic equality would add well-order product and
finite-factor infrastructure without shortening the final join.

### 10. Single stabilized Hartogs injection (`prop:stabilized`, lines 528--569)

**Status:** not separately targeted.  Its proof-specific content is split
between the pointwise representative bridge and the canonical graph.

The exact range-coverage theorem must state the formula in the “Exact final
fixed-block graph” section.  Once it is frozen, `hnfixedblockhnqcoverinjndv`
constructs the injection without any collected family of witnesses.

### 11. Unconditional fixed-block replay (`thm:unconditional-fixed-block-replay`, lines 574--644)

**Status:** complete and frozen, including common-range coverage.

The representative-level transport theorem already frozen is

```text
cfbhnqinjcodecoverndv:
  u e. HWCN P
  k : (2nd ` u) -1-1-> Y
  |-
  (HNQInc(P,P u. Y) ` [u] HWNIso P) e.
    ran HNQInc(Y,P u. Y).
```

The pointwise proof must do the following for one source quotient value:

1. use reverse coverage of `Theta` to obtain a represented code over
   `A0 = ~P1^3(~P X)`;
2. lower its supported carrier to a well-ordered `A C_ ~P X`;
3. apply the first-difference theorem and the product comparison to obtain
   `~P1^3 A -1-1-> ~P^2 HNOrd X`;
4. raise/transport the representative code through the three `HNSIQuoMap`
   stages;
5. invoke the deduction form of `cfbhnqinjcodecoverndv` and eliminate the
   local injection witness;
6. generalize pointwise to the exact range inclusion.

Nothing in this list chooses one map for every quotient element.  The final
verified exports are

```text
cfbhnpw13pointcoverndv
cfbwppfixedblockhnqimagecoverndv
cfbwppfixedblockhnqgraphinjndv
cfbwppfixedblockhnqinjexndv
wppfiniteblocknotwppndv.
```

### 12. Homogeneous stabilized inequality (`lem:homogeneous`, lines 646--688)

**Status:** the generic `h/e` statement is not required by the concrete
Metamath route.  Its exact width-six normalization and cancellation are
frozen.

```text
cfbsourceledgerndv |-
  Nc(~P1^3 HNOrd(~P X0)) = T_c^9 HNCard 1c.

cfbtargetledgerndv |-
  Nc(HNOrd(~P^2 HNOrd X0)) =
    T_c^5 HNCard(~P^2 HNOrd(~P1 1c)).

cfbfixedblockcancel3ndv |-
  (T_c^9 HNCard 1c <_c T_c^5 Q ->
   T_c^6 HNCard 1c <_c T_c^2 Q).
```

The special equality `HNCard(~P 1c) = HNCard 1c` is frozen as
`cfbhncardpw1ceqndv`, using `ncpw1c` and `hncardnceqndv`.  Every
cancellation removes a common prefix only.

### 13. Domain width (`lem:domain-width`, lines 725--744)

**Status:** no new generic formalization is needed.  The finite width is
specialized to six and included in the existing concrete evaluator and
stopped-growth package.

### 14. Least-orbit obstruction (`lem:orbit`, lines 748--829)

**Status:** frozen inside the width-six stopped-Gamma terminal.  Do not replay
the generic orbit proof in the cumulative branch.

### 15. Universal-chain threshold (`lem:threshold`, lines 831--893)

**Status:** frozen at the exact F6 point.  The public terminal interface is

```text
wppconcrete6notwppfrompointndv.1 $e |-
  WPP ->
    T_c^6 HNCard 1c <_c
    (WPPConcrete6Fn ` T_c^7 HNCard 1c).

wppconcrete6notwppfrompointndv $p |- -. WPP.
```

### 16. Main theorem and corollary (`thm:main`, lines 895--910)

**Status:** terminal logic is frozen.  `cfbfixedblocknotwppfrominjndv`
packages the exact fixed-block injection into the F6 point and immediately
invokes `wppconcrete6notwppfrompointndv`.

## Exact source and target ledger at the concrete base

Let

```text
D = HNCard 1c
Q = HNCard ~P ~P HNOrd ~P1 1c.
```

For `X0 = ~P1^6 1c` the actual set-coded graph has cardinal comparison

```text
Nc(~P1^3 HNOrd(~P X0)) <_c
Nc(HNOrd(~P^2 HNOrd X0)).
```

The frozen equalities rewrite this, without WPP or monotonicity, to

```text
T_c^9 D <_c T_c^5 Q.
```

`tc3lecan` cancels exactly the common outer `T_c^3`:

```text
T_c^6 D <_c T_c^2 Q.
```

The canonical well-order exported by `cfbtargethnordweexplicitndv`, the
shifted outer Hartogs step `hncardsuccshiftedndv`, and the exact value of
`WPPConcrete6Fn` turn this into

```text
T_c^6 D <_c (WPPConcrete6Fn ` T_c^7 D).
```

This is the sole premise of the stopped-Gamma contradiction.

## Concrete product bypass and direct terminal consumption

The concrete product theorem can be consumed without changing any terminal
normalizer.  Its exact required formula is

```text
HNCard
  ( ( ( ~P1 ~P1 ~P1 ~P1 ~P1 ~P1 1c
          X._k
        ~P1 ~P1 ~P1 ~P1 ~P1 ~P1 1c )
      X. Nn ) ) <_c
T_c T_c HNCard
  ~P1 ~P1 ~P1 ~P1 ~P1 ~P1 1c.
```

It plugs into the `X = X0` instance of `cfbfdwppcarrierinjndv`; no generic
product hypothesis survives after specialization.  The resulting
representative carrier map has the exact target required by the final
common-ambient base:

```text
~P1 ~P1 ~P1 A -1-1-> ~P ~P HNOrd X0.
```

Consequently, once the representative-coverage theorem is frozen, the final
replay order is exactly:

1. include `cfb_target_terminal_frozen_checkpoint.mm`;
2. replay `threshold_tc2_injection_parent_free_suffix.mm`;
3. replay `concrete_universal_product_absorption_parent_free_suffix.mm` and
   use `cfbliteralp16onehncardboundndv` directly;
4. replay the pointwise carrier/representative-coverage parent-free suffix;
5. instantiate the coverage theorem at `X0`;
6. apply `wppfixedblockhnqgraphinjndv` with `cfbpw16oneexndv`;
7. existentially introduce its named canonical graph;
8. apply `cfbfixedblocknotwppfrominjndv`.

There is no need to pass through `Nc`, the homogeneous `h/e` language, or a
global `HL-XPORT` theorem after step 4.

## Safest replay policy

1. Treat `cfb_target_terminal_frozen_checkpoint.mm` as the sole cumulative
   parent of the final join.
2. Rebase each independent branch to this parent by copying only its
   parent-free suffix.  Never include two full frozen checkpoints that share
   the same large ancestor.
3. Freeze the concrete product comparison first.
4. Freeze the pointwise carrier theorem next, with the product comparison as
   an explicit hypothesis if necessary.
5. Freeze the three-step representative bridge and the exact WPP range
   coverage theorem.
6. Add only a thin final suffix: named graph injection, existential wrapper,
   and `cfbfixedblocknotwppfrominjndv`.
7. Run both independent verifiers and require zero trusted new assertions.

## Implemented non-overlapping prerequisite

This audit branch implemented and froze the complete target-side landing
adapter rather than duplicating first-difference or coverage work:

```text
cfbtargetledgerndv
cfbfixedblockledgercmpndv
cfbfixedblockcancel3ndv
cfbfixedblockouterhartogsndv
cfbfixedblockf6pointfrominjnowendv
cfbfixedblocknotwppfrominjndv.
```

The final well-order premise was eliminated by the concrete canonical
relation theorem `cfbtargethnordweexplicitndv`.  Thus the final coverage
branch need export only the exact injection; it need not construct or pass a
separate well-order witness for the target Hartogs carrier.

## Remaining exit criterion

### Projection-safe factorization frozen on 20 August

The pre-powerset Hartogs/column tail has now been split into two genuinely
projection-independent frozen interfaces:

```text
cfbhartogsfromrangehwcndv
  X e. V
  S e. V
  Nc S e. HWCards V
  (WPP -> Nc S <_c Nc(((X X._k X) X. Nn)))
  HNCard(((X X._k X) X. Nn)) <_c T_c^2 HNCard X
  -------------------------------------------------
  WPP -> E. f f : S -1-1-> HNOrd X

cfbcolumnliftinjndv
  X e. V
  A e. V
  D e. V
  T_c^2 Nc A <_c Nc(~P ~P D)
  (WPP -> E. f f : ~P1 D -1-1-> HNOrd X)
  -------------------------------------------------
  WPP -> E. k k : ~P1^3 A -1-1-> ~P ~P HNOrd X.
```

The corresponding cumulative checkpoints are dual-verified with no trusted
new assertions:

```text
generic_hartogs_adapter_frozen_checkpoint.mm
  SHA-256 99D9D76555C3D527AE0E074573BD06B76DC6E476D1101030DB4439DED5EE65BF
  7890 proofs / 15924 statements

generic_column_lift_frozen_checkpoint.mm
  SHA-256 875030F1D5F0B8F44FCC110192E3BA57B27E826C54F03040C8D019F503722595
  7891 proofs / 15930 statements.
```

The generic first-difference source bundle is also dual-verified:

```text
cfbfdpw1literalproductbundleimndv
  R We A ->
    ((~P1 FDif(R,A,X) e. V /\
      Nc(~P1 FDif(R,A,X)) e. HWCards V) /\
     (WPP ->
       Nc(~P1 FDif(R,A,X)) <_c
       Nc(((X X._k X) X. Nn)))).
```

It is not sound to specialize this displayed bundle directly at the two
class values `fst(u)` and `snd(u)`.  `vtocl2` requires an explicit formula
equivalence under the two projection equalities, while the current frozen
API contains no `FDif` congruence theorem.  The available `df-fdif`,
`elfdif`, and `fdifequnirange2x` do not by themselves discharge that
equivalence.

The smallest projection-safe residual was exactly the temporary contract
used by `final_coverage/projected_carrier_pre.mm`:

```text
cfbfdwppcarrierimpndv
  R e. V
  A e. V
  X e. V
  HNCard(((X X._k X) X. Nn)) <_c T_c^2 HNCard X
  -------------------------------------------------
  ((R We A /\ A C_ ~P X) ->
    (WPP -> E. k k : ~P1^3 A -1-1-> ~P ~P HNOrd X)).
```

Here every `FDif` occurrence has been consumed before projection.  Once this
one implication is verified, the already staged simultaneous `vtocl2`
wrapper needs only `breq12d`, `sseq1d`, three `pw1eq` steps, and `f1eq2`;
`hwcnweclndv` and `hwcnbaseclndv` then discharge its antecedent.  No
first-difference congruence or carrier-pair substitution is required.

That residual is now discharged by the dual-verified live theorem
`cfbfdwppcarrierimpndv` in `coverage_packaging_alt/carrier_imp_live.mm`:

```text
SHA-256 17B687ADBCF4D7534FB8D5DF5FB2E7FBE28958C8610BDD103C1B39E6B7EF50F3
7893 proofs / 15935 statements
mandatory DVs: R-A, R-X, A-X, R-k, A-k, X-k.
```

Thus the remaining coverage work begins strictly after the fresh-pair
implication: rebase the staged projection wrapper, apply it to each normalized
Hartogs code, and finish the already designed common-ambient image-coverage
and canonical-graph exports.

The former residual is discharged.  `cfbhnpw13pointcoverndv` supplies the
pointwise formula, `cfbwppfixedblockhnqimagecoverndv` packages the range
inclusion, and `cfbwppfixedblockhnqgraphinjndv` supplies the explicit
canonical graph.  `cfbwppfixedblockhnqinjexndv` existentially closes that
graph and the four-application terminal proves `-. WPP`.

## Final frozen publication endpoint

```text
cumulative checkpoint:
  integration_audit/wppfiniteblocknotwpp_frozen_checkpoint.mm
  SHA-256 266B9DC2CBBA5ECCA2C0930BA4D12D026EF720E5947AD214153A6C40BF0B8F62

parent-free suffix (parent: cfb_image_graph_frozen_checkpoint.mm):
  integration_audit/wppfiniteblocknotwpp_parent_free_suffix.mm
  SHA-256 3691F1C64E1DA76BE983A83A02EC5DDADB063891ADD8D93439BA8A00E0BEEEAE

public theorem:
  wppfiniteblocknotwppndv $p |- -. WPP $.
  essential hypotheses: 0
  mandatory DV pairs: 0

primary verifier:   OK 7973 proofs, 16074 statements
secondary verifier: OK 7973 proofs, 16074 statements
declared-parent rebase: same dual-verifier counts
```

The machine-readable manifest is
`integration_audit/wppfiniteblocknotwpp_frozen_checkpoint.audit.json`.
