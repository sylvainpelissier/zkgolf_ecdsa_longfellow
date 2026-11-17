# Proof plan: the `circuit_baseline` ECDSA circuit

Status: planning document. No proofs are implemented yet.
Branch note: this document lives on `mistral-ecdsa-plan`. All source references are
to the ref `origin/circuit_baseline` (commit `3a1bd20`, "Add experimental ECDSA
circuit baseline and representation proofs"). **No other branch of this repo is
fetched, merged, or checked out**: the plan reads that branch's content through
`git show origin/circuit_baseline:<path>` and, when implementation starts, a work
branch will be created directly from `origin/circuit_baseline`.

## 0. Target and ground rules

- **Circuit under proof**: `Baseline.main : Var Input Fp → C Unit` in
  `Baseline/Circuit.lean` on `origin/circuit_baseline` — the gate-for-gate Clean
  lowering of Longfellow's `verify_signature3`
  (`lib/circuits/ecdsa/verify_circuit.h` @ `4fe092be…`) over `Fp = ZMod p`
  (P-256 base field; `p` from `Challenge.Specs.ECDSAP256`). `Input`
  (`Challenge/Instances/ECDSA_P256_Digest/Interface.lean`) is 1037 field
  elements: 3 statement fields (`pkX, pkY, digest`) + 1034 source-witness fields
  (`rx, ry, rxInv, sInv, pkInv, pre[8], bi[256], intX/intY/intZ[255]`).
- **"Prove" = the seven trusted obligations** of
  `Challenge/Instances/ECDSA_P256_Digest/Challenge.lean`, instantiated at
  `main := fun inp => Baseline.main inp` (wrapped to return the unit output):
  1. `elaborated : ElaboratedCircuit Fp Input Output main`
  2. `soundness : GeneralFormalCircuit.Soundness Fp main Assumptions Spec`
     (`Assumptions = True`; `Spec input () data = ValidEcdsaWitness (witness input)
     { X := pkX, Y := pkY } digest n params`)
  3. `completeness : GeneralFormalCircuit.Completeness Fp main ProverAssumptions ProverSpec`
     (`ProverAssumptions input data hint = Spec input () data`; `ProverSpec = True`)
  4. `mainCost : circuitCost main ⟨11375, 12415⟩` (literal-lowering score 23,790,
     per `Baseline/README.md` and `lake exe baseline --count-only`)
  5. `isR1CS : Challenge.CostR1CS.isR1CS main`
  6. `witgenIsIR : Challenge.WitgenIR.witgenIsIR main`
  7. `computableWitness` and `requirementsChannelsLawful`
- **Axiom hygiene**: every theorem must depend only on `propext`,
  `Classical.choice`, `Quot.sound` — no `sorryAx`, no `native_decide`
  (enforced by `scripts/check_axioms.py`; P-256 primality comes from the vendored
  Pratt certificate `ECDSA.Pratt`).
- **Toolchain**: Lean `v4.34.0`; dependencies pinned by the branch's
  `lake-manifest.json` (clean @ `93c9d1ef…`, mathlib @ `5ed29652…`).
- **Verification commands**: `lake build`; `lake exe baseline --count-only`
  (must print allocations 11,375, rows 12,415, score 23,790, 0 R1CS violations);
  `lake exe baseline` (252-vector differential test must stay green);
  `python3 scripts/check_axioms.py`.
- **Key semantic facts** (Clean @ `93c9d1ef`): `GeneralFormalCircuit.Soundness`
  (`Clean/Circuit/Formal.lean:154`) concludes both `Spec …` **and**
  `Operations.Requirements env ops` (`Clean/Circuit/Operations.lean:820`) — the
  latter licenses reading each `witness e c` operation as "wire = `c.eval env`".
  `circuitCost`/`CostIs` (`Challenge/Utils/CostR1CS.lean:300-330`) ships
  compositional lemmas (`CostIs.bind`, `CostIs.witnessVector`,
  `operationCount_append`). `Challenge/Utils/WitgenIR.lean` provides
  `UsesIRCirc.*` combinators; every witness in `Baseline.main` is
  `Circuit.witnessField`, so `witgenIsIR` is purely structural.
- **Vendored spec support to reuse** (`vendor/longfellow/ECDSA/` on the branch):
  `EcdsaCircuit.lean` (`ValidEcdsaWitness`, `val3` + `val3_cast_eq` /
  `cast_val3_eq`, `muxPointF_cast_eq`, `EcdsaLoopConstraintsF_cast_eq`, …);
  `Ecdsa.lean` (`exists_bi`, `exists_loop_witness`, `exists_pre_computation`,
  `muxPoint_correctness`, `ecdsa_algebraic_equivalence`,
  `loop_result_eq_linear_combination`, …); `Nat.lean` (`reconstructE/R/S`,
  `natR/natS`, `natToBits`, `padBits`); `EC.lean` (`addE`/`doubleE`/`muxPoint`/
  `IsPointEquality`/`infinityPoint` — the functions the spec quantifies over).
- **Scope**: primary target is `Baseline.main` (literal lowering, 23,790).
  `Optimized.main` (`Baseline/Optimized.lean`, 19,630) is a drop-in alternative;
  the same plan applies with its boolean-selector and quotient-gate gadgets
  swapped into Phases 3-4 (its local lemmas live in
  `Baseline/OptimizationLemmas.lean` and cover only the comparator semantics).

## 1. Phase 1 — Setup (one task)

**T1.1 (setup)**: create the implementation branch from
`origin/circuit_baseline` only (e.g. `git worktree add ../ecdsa-proof
origin/circuit_baseline`, or `git switch -c proof/circuit-baseline
origin/circuit_baseline`) — do not fetch or merge any other branch. Run
`lake build`, `lake exe baseline --count-only`, `lake exe baseline`,
`python3 scripts/check_axioms.py`; record outputs. Add a `Proofs/` library to
`lakefile.lean` with skeleton modules (`Proofs/Semantics.lean`,
`Proofs/Algebra.lean`, `Proofs/Mux.lean`, `Proofs/Comparator.lean`,
`Proofs/Loop.lean`, `Proofs/Assembly.lean`, `Proofs/Cost.lean`,
`Proofs/Structure.lean`, `Proofs/Main.lean`) that compile.
**Acceptance**: clean build on the new branch; counts 11,375 / 12,415 / 23,790
reproduced; differential suite green.

## 2. Phase 2 — Lowering-semantics infrastructure (parallel)

**T2.1 (`Proofs/Semantics.lean`)** — generic lemmas for the lowering combinators
in `Baseline/Circuit.lean` (`mat`, `mm`, `pm`, `assertZeroLazy`, `flat`,
`isProd`, `sc`, `cst`, `constVal`), by induction on `Expression Fp` and on the
`Circuit` bind skeleton:
- invariant: `mat e` returns an affine expression (`Challenge.CostR1CS.Affine`)
  and, given `Operations.Requirements env ((mat e).operations 0)`, its result
  `r` satisfies `r.eval env = e.eval env`;
- `assertZeroLazy e`: given Requirements + `ConstraintsHold.Soundness env`,
  conclude `e.eval env = 0`;
- equation lemmas for `Circuit.bind` and for the `for i in [0:256] do` loop
  (constant-length, so operations append), plus `Requirements` append lemmas.
**Acceptance**: later phases can consume these without unfolding `Baseline.main`.

**T2.2** — extraction helpers: from `Requirements env ops` + op list, per-`witness`
facts (`wire_k = FExpr.eval env`); from `ConstraintsHold.Soundness env ops`,
per-`assert` facts (`e.eval env = 0`); `toFlat` bridges
(`operationsIsR1CS_iff_toFlat`, `operationsUseIR_iff_toFlat`).

## 3. Phase 3 — Algebraic gadget equivalence (parallel)

**T3.1 (`Proofs/Algebra.lean`)** — circuit `addE`/`doubleE` agree with spec
`_root_.addE`/`doubleE` (`EC.lean:225`/`:184`): given the gadget's Requirements
and constraint holds, the returned triple evaluates coordinatewise to
`addE p1 p2 params` / `doubleE p params` (extract the 6 resp. 5 `mm`-wire
equations, then `simp [addE]` + `ring`). Verify coordinate-by-coordinate first;
a mismatch is a finding to report, not to patch silently.

**T3.2 (`Proofs/Mux.lean`)** — Lagrange mux correctness:
- `lagrangeBasis` interpolation: `Σ_j basis_i[j] * x^j` at `x = 2v-7` equals
  `δ_{i,v}` for `v ∈ 0..7` (compute the constant tables with `decide`/`norm_num`
  on `ZMod p` — allowed; `native_decide` is not);
- hence `muxEval (muxCoeffs basis8 arr) xl = arr[v]` when `bp = 2v-7`; applied to
  `arrX/arrY/arrZ/arrE/arrR/arrS` this gives `tx,ty,tz = muxPointF (bi_i)` and
  `ebi/rbi/sbi ∈ {0,1}` with the right bit values, via `muxPointF_cast_eq` /
  `val3_cast_eq`;
- range polynomial: `muxEval cV xl = ∏_{i<8} (bp - (2i-7))` (by `ring`), so
  `assertZero (muxEval cV xl)` implies `bp = 2j-7` for some `j` (field
  zero-product property), hence `bi_i = (j : Fp)` and `val3 bi_i = j` — the
  selector-range conjunct of `ValidEcdsaWitness`.

**T3.3 (`Proofs/Algebra.lean`)** — scalar reconstruction: induction over the
256-step accumulators `est := ebi + 2*est` (also `rst`, `sst`) proves
`est.eval = reconstructE (bi.map val3)` etc. (`Nat.lean:218-224`), given all
`bi_i ∈ 0..7` from T3.2.

**T3.4 (`Proofs/Comparator.lean`)** — `ltReduce` correctness for the literal
baseline: give `ltReduce nb a i0 i1` a semantic spec (eq/lt expressions over
boolean bits) and prove by induction on the recursion that `lt = 1` iff the bit
segment is lexicographically `<` the bound's segment; from
`assertZeroLazy (ltR - 1)`, `assertZeroLazy (ltS - 1)` conclude
`natR (bi.map val3) < n` and `natS … < n` (bits from `rbits`/`sbits`, boolean by
T3.2). Do not reuse `Baseline/OptimizationLemmas.lean` directly — it covers only
the optimized comparator.

**T3.5** — small wrappers: `pointEquality` ⇒ `IsPointEquality`; `isOnCurve` ⇒
`AffinePoint.IsOnCurve`; inverse asserts ⇒ `rx*rxInv = 1`, `sst*sInv = 1`,
`pkX*pkInv = 1`; 4× `addE` + `pointEquality` ⇒ `ValidPreComputationExact`.

## 4. Phase 4 — The 256-step loop (one focused task, splittable)

**T4.1 (`Proofs/Loop.lean`)** — by induction on `List.range 256` (via the T2.1
plumbing), prove the invariant: at step `i`, `(ax,ay,az).eval` equals the spec
loop accumulator and the `intX/intY/intZ` wires at `i` equal the next
accumulator's coordinates — i.e. `EcdsaLoopConstraintsF infinityPoint true bi …`
and `ecdsaLoopResultF` at `i = 255` with `X = 0 ∧ Z = 0`. Uses T3.1, T3.2 and
`EcdsaLoopConstraintsF_cast_eq` to move between `bi : List Fp` and
`bi.map val3`. Split: T4.1a one-step lemma; T4.1b induction + the `i = 255`
special case (`assertZeroLazy nx` / `nz` instead of int-witness equalities).

## 5. Phase 5 — Assembly of soundness / completeness (one task)

**T5.1 (`Proofs/Assembly.lean`)** — instantiate
`main := fun inp => Baseline.main inp >>= fun _ => pure (unit output var)`.
- *Soundness*: from `ConstraintsHold.Soundness` + `Requirements`, apply
  T2.1-T4.1 to assemble every conjunct of `ValidEcdsaWitness (witness input) …`
  (length conjuncts are `rfl` from the `Vector` fields; selector range from
  T3.2; loop from T4.1; final `X = 0 ∧ Z = 0`, reconstructions, on-curve,
  inverses, `natR/natS < n` from T3.3-T3.5). Conclude `Spec input () data`.
- *Completeness*: given `Spec input () data`, show
  `ConstraintsHold.Completeness env ops` under
  `UsesLocalWitnessesCompleteness`: every `witnessField` generator is an FExpr
  over input vars + previously allocated wires, so default witnesses satisfy
  each wire equation, and each assert reduces (forward direction of the same
  T3.x equalities) to a spec conjunct. Vendored existence lemmas (`exists_bi`,
  `exists_loop_witness`, `exists_pre_computation`, `ecdsa_algebraic_equivalence`
  in `Ecdsa.lean`) supply the mathematical content.

## 6. Phase 6 — Cost, R1CS shape, IR, computability, channels (parallel)

- **T6.1 (`Proofs/Cost.lean`)** — `mainCost`: prove
  `CostIs (main input) ⟨11375, 12415⟩` via `CostIs.bind` / `.witnessVector` /
  per-gadget counts (`addE` = 12 rows / 6 allocs, `doubleE` = 11 / 5, one
  alloc + row per `mm` product, mux powers and `mat`s, `assertZeroLazy`
  accounting, `ltReduce` node counts, final asserts), summed with `Count.add`
  simp lemmas + `omega`. Performance guard: count per gadget, never `decide` on
  the whole ~12k-row list, no `native_decide`. Cross-check against
  `lake exe baseline --count-only`.
- **T6.2 (`Proofs/Structure.lean`)** — `isR1CS`: every assert from `mat e` is
  `.mul a' b' - w` with `a' b'` affine (`r1csProducts = 1`); every assert from
  `assertZeroLazy e` has ≤ 1 non-constant-factor product of affine forms; the
  direct `assertZero (muxEval cV xl)` has all-constant coefficients
  (`arr = [0,…,0,1]`) hence 0 products; compose via
  `operationsIsR1CS` append lemmas. Also `requirementsChannelsLawful` (no
  lookups/interactions ⇒ structural) and `elaborated` (Clean's
  `ElaboratedCircuit` API).
- **T6.3** — `witgenIsIR` via `UsesIRCirc.witnessField` + bind/`forM`
  composition lemmas (all witnesses are `witnessField`, no `.native`).
- **T6.4** — `computableWitness`: each `witnessField e` reads only input vars and
  earlier-allocated wires (program-order allocation), so under
  `OnlyAccessedBelow n` the generator agrees; use Clean's `ComputableWitnesses`
  lemmas (`Clean/Circuit/Subcircuit.lean:430`).

## 7. Phase 7 — Packaging & audit (one task)

**T7.1 (`Proofs/Main.lean`)** — export the seven theorems with exactly the types
of `Challenge/Instances/ECDSA_P256_Digest/Challenge.lean`; build the
`GeneralFormalCircuit` value; `#print axioms` each theorem (only the three
standard axioms); add a `Tests/ProofAxioms.lean` wired into
`scripts/check_axioms.py`; run the full check suite plus `lake exe baseline`;
document the architecture in `Proofs/README.md`.

## 8. Task dependency graph

```
T1.1 setup
 └─ T2.1/T2.2 semantics ─┬─ T3.1 addE/doubleE ─┐
                         ├─ T3.2 mux ─┬─ T3.3 reconstruct ─┤
                         │            └─ T3.4 comparator ─┼─ T3.5 wrappers ─┬─ T4.1 loop ─→ T5.1 assembly ─→ T7.1
                         └─ T6.1..T6.4 (cost/structure/IR/computable) ────────────┴──────────────────→ T7.1
```

Phases 2-3 and Phase 6 are parallelizable across subagents (disjoint files);
T4.1 depends on T3.x; T5.1 depends on all semantic tasks; T6.x are independent
of T5.1.
