# `theories/simulations/ctxrefine` — contextual refinement and the top-level adequacy theorems

Logical path: `CRIS.simulations.ctxrefine`.

The end of the chain. Everything below the simulation tower exists to
establish the two theorems in this directory:

- **`ISim_closed_adequacy`** — an `ISim.t closed` proof gives whole-program
  refinement;
- **`main_adequacy`** — an `ISim.t open` proof gives *contextual* refinement,
  i.e. refinement under every module context `Ctx`.

---

## `CtxRefine.v` — the definitions

- `refines_lmod ms_tgt ms_src : Prop` — plain behaviour inclusion between two
  compiled `LMod.t`s.
- **`Beh M t : iProp Σ`** (sealed) — "for every valid resource `r'` extending
  the current one, the trace `t` is a behaviour of `Mod.to_lmod M r'`". Built
  directly as a `uPred`. Introduced in the `Unreleased` CHANGELOG entry
  (`Add Beh : Mod.t -> Tr.t -> iProp Σ`).
- **`refines Mt Ms := ⌜Mod.wf Mt⌝ → ⌜Mod.wf Ms⌝ ∧ (winv (∅,∅) -∗ ∀ t, Beh Mt t -∗ Beh Ms t)`** —
  refinement, phrased with `Beh` (the CHANGELOG notes this redefinition is
  equivalent to the previous one).
- **`ctx_refines Mt Ms := ∀ Ctx, refines (Mt ★ Ctx) (Ms ★ Ctx)`**.

## `BehFacts.v`

`Beh_intro` — if `M` is well-formed and `t` really is a behaviour of
`Mod.to_lmod M r`, then `Own r ∗ winv (∅,∅) ⊢ Beh M t`. (Getting from a
*specific* resource `r` to *every* extension `r'` uses reflexivity —
`ISim_refl` → `ISim_adequacy` → `lsim_adequacy` → `gsim_adequacy`.)
`Beh_elim` — the converse extraction.

## `ClosedAdequacy.v` — whole-program adequacy

- `Own_split'` — split a resource along an entailment `Own r ⊢ P ∗ Q`,
  keeping validity of the `P` half.
- **`gsim_closed_adequacy` : `gsim_mod Ms Mt ⊢ refines Mt Ms`**.
- **`lsim_closed_adequacy` : `lsim_mod Ms Mt ⊢ refines Mt Ms`** (factors
  through `gsim_mod` via `lsim_adequacy`).
- **`ISim_closed_adequacy` : `ISim.t closed Ms Mt Ist ⊢ refines Mt Ms`**
  (factors through `lsim_mod` via `ISim_adequacy`).

The three were renamed/added in the `Unreleased` CHANGELOG entry
(`closed_adequacy` → `ISim_closed_adequacy`; `gsim_closed_adequacy` and
`lsim_closed_adequacy` are new).

## `MainAdequacy.v` — contextual adequacy

The hard direction: an *open* simulation must be shown to survive composition
with an arbitrary context.

- Sandbox helpers `inv_sandbox_ktr`, `inv_sandbox_event`, `inv_sandbox_tau` —
  a sandboxed tree is unchanged by re-sandboxing at the head, which is what
  lets the context's events pass through untouched.
- `Own_Ist` — resource bookkeeping for splitting the state invariant between
  the module and the context.
- **`msim_ctx`** — the core lemma. Given that `ms`'s scopes are contained in
  `mt`'s, that all three states respect their scopes, that both trees are
  already sandboxed to `mt`'s scopes, and that both compositions are
  well-formed, an `msim open` between `ms` and `mt` lifts to an `msim` between
  `ms ★ ctx` and `mt ★ ctx` with the product invariant
  `IstProd (IstSB (scopes mt) Ist) (IstSB (scopes ctx) IstEq)` — the context's
  half of the state is simply *equal* on both sides.
- **`isim_ctx`** — the same statement one level up, in the logic.
- **`ISim_ctx`** — and one level up again:
  `ISim.t open ms mt Ist ⊢ ISim.t contextual (ms ★ ctx) (mt ★ ctx) (IstProd …)`.
- **`main_adequacy` : `ISim.t open Ms Mt Ist ⊢ ctx_refines Mt Ms`** —
  three lines: introduce the context, apply `ISim_closed_adequacy`, apply
  `ISim_ctx`.

## `CtxRefineFacts.v` — the algebra of contextual refinement

- `refines_mod_PreOrder` (for the `Prop`-level `refines_lmod`),
  `refines_refl`, `refines_trans`.
- Vertical composition: `ctxr_refl`, `ctxr_trans`, `ctxr_refines`
  (contextual refinement implies plain refinement, by instantiating the
  context with `⌽`).
- Algebraic equalities, all immediate from the fact that `★` is a commutative
  monoid *up to Leibniz equality*: `ctxr_comm`, `ctxr_assoc`, `ctxr_swap`.
- `elim_module M : ⊢ ctx_refines M ⌽` — any module refines the empty one
  (proved with `main_adequacy` and `cStartModSim`).
- Frame rules `ctxr_frameL`, `ctxr_frameR`; horizontal composition
  `ctxr_compose_hor`; mixed composition `ctxr_compose_mix`.
- **`ctx_refines_BiProset : BiProset (iProp Σ)`** — the punchline: modules,
  with `ctx_refines` as the hom-family, `⌽` as the unit and `★` as the tensor,
  form a `(iProp Σ, ∗, emp)`-enriched symmetric monoidal preorder in the sense
  of [`theories/lib/BiEnrichedProset.v`](../../lib/BiEnrichedProset.v). This is
  what makes the `j`-tactics (`jSplitL`, `jFrame`, `jApply`, …) usable for
  composing refinement proofs — and why the legacy `ctxr_norm` / `ctxr_rotate`
  / `ctxr_drop` tactics were removed (see the `Unreleased` CHANGELOG entry).
- `refines_adequacy` — extract the raw, `Prop`-level statement:
  `winv (∅,∅) ∗ refines Mt Ms ⊢ ⌜∃ rs, ✓ rs ∧ refines_lmod (Mod.to_lmod Mt ε) (Mod.to_lmod Ms rs)⌝`.
