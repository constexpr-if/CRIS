# `theories/common` — events, behaviours, and the global preludes

Logical path: `CRIS.common`.

This directory fixes the *vocabulary* of CRIS: which events a program may
trigger, what a program's observable behaviour is, which ghost resources the
concurrency model needs, and the reduction machinery used to normalise
interpreter applications. It also provides the two "import everything"
headers, `Common.v` and `CRIS.v`.

---

## `Events.v` — the event signatures

The heart of the directory. Everything CRIS programs can do is one of these
events.

**Core (non-deterministic + external) events.**

```coq
Variant coreE : Type → Type :=
| Choose (X : Type) : coreE X      (* demonic/angelic branching, "our" choice *)
| Take   (X : Type) : coreE X      (* the adversary's choice *)
| IO {O I} (fn : string) (args : O) : coreE I.   (* observable interaction *)
```

**Keys and low-level state.** `key := string * string` (module name × function
name), with `sf s f := (s,f)` and the notation `s ↯ f`.
`lstateT := gmap key (option Any.t) * Any.t` is the low-level state (a
per-key private store plus one global cell); `lstateE` has the single
constructor `SUpdate (run : lstateT → lstateT * V) : lstateE V`, from which
`sPut` and `sGet` are derived.

**Calls and concurrency.**

```coq
Variant callE : Type → Type :=
| Call (fn : string) (args : Any.t) : callE Any.t
| Spawn (fn : string) (args : Any.t) : callE nat
| Yield (tid : nat) : callE unit
| GetTid : callE nat.
```

**The two program signatures.**
- `lmodE := callE +' lstateE +' coreE` — the *low-level* (implementation)
  signature.
- `crisE := agE +' callE +' pgE +' coreE` — the *specification* signature,
  where
  - `pgE` is the per-key program state: `SPut (k : key) (v : Any.t)` and
    `SGet (k : key)`;
  - `agE` carries separation-logic obligations:
    `Assume (P : iProp Σ)`, `AssumeRes (r : Σ)`, `Guarantee (P : iProp Σ)`.
  Both are parameterised by a `GRA` `Σ`.

**Derived combinators (`Section WRAP`, over any `E` with `coreE -< E`).**
`assumeK`, `guaranteeK`, `assume`, `guarantee`, `unwrapUK`, `unwrapNK`,
`unwrapU`, `unwrapN`, `triggerUB`, `triggerNB`, `unleftU`, `unleftN`,
`unrightU`, `unrightN`, with the notations `f?` (`unwrapU`) and `f!`
(`unwrapN`). "U" = *undefined behaviour* (a `Take False`, i.e. the adversary
must supply the impossible), "N" = *no behaviour* (a `Choose False`). The
accompanying rewriting lemmas relate the `K`-suffixed continuation-passing
forms to the plain ones and push `bind` inside: `assume_assumeK`,
`assumeK_assume`, `assumeK_bind`, `guarantee_guaranteeK`,
`guaranteeK_guarantee`, `guaranteeK_bind`, `unwrapU_unwrapUK`,
`unwrapUK_unwrapU`, `unwrapUK_bind`, and the `N` counterparts.

**`Section FancyReal`.** `RealUpdate pp` is the epilogue used by prophetic
specifications: it chooses a resource `pr`, `Guarantee`s that every `(P,Q)`
in the relation `pp` admits `P ==∗ Own pr ∗ Q`, and then `AssumeRes pr`. The
body is wrapped in `Seal.sealing CRIS_FancyReal` so it does not accidentally
unfold. With `RealUpdateK`, `RealUpdate_RealUpdateK`, `RealUpdateK_RealUpdate`,
`RealUpdateK_bind`.

**Typed function signatures.** The phantom record `fntyp_t A R`, `fntyp`,
`fnsig_t A R := string * fntyp_t A R`, `fnsig`, `fn_name`, `fn_type` (a
coercion). `Section SYNTAX` then gives the surface syntax used to write
modules: `ccallU` / `ccallN` (call a `fnsig_t` with automatic
`Any.upcast`/`downcast`), `cfunU` / `cfunN` (define a function body of
type `Any.t → itree E Any.t`), and `cput`, `cgetU`, `cgetN` for `pgE`.

**Case analysis on trees.** `case_itrL` (an `itree lmodE R` is a `Ret`, a
`Tau`, or a bind of a `coreE`/`lstateE`/`callE` trigger) and `case_itrH` (the
eight-way version for `itree crisE R`). These are the workhorses of every
simulation proof.

**Event masks (sandboxing).** `emask := ∀ X, crisE X → bool` with
`msk_true`; `msk_scp scp msk` (restrict `SPut`/`SGet` to keys whose module is
in `scp`); `msk_real msk` (forbid `Assume`, and only allow `Take` at
propositional types); `msk_pure`; the pointwise `msk_and`, `msk_or`; and the
predicates `img_msk` (the mask admits all `Take`/`Choose`/`Assume`/
`AssumeRes`/`Guarantee`), `call_msk` (the mask ignores call arguments), and
the ordering `msk_sub`.

## `Behavior.v` — observable behaviours

Defines what a *closed* program (an `itree coreE Any.t`) does.

- Observation labels: `outinE ::= obs_io fn O I args rv` (a completed
  interaction) and `hangE ::= obs_hang fn O args` (an interaction that never
  returns).
- `Tr.t` — the coinductive trace type:
  `done (retv : Any.t) | abort | spin | hang (e : hangE) | interact (hd : outinE) (tl : t)`.
- `Beh.t := Tr.t -> Prop` and refinement `Beh.improves src tgt := tgt <1= src`
  ("`src` has at least the behaviours of `tgt`").
- `_state_spin` / `state_spin` (`paco1`) — the tree diverges silently: `Tau`
  forever, with `Choose` needing *some* branch to spin and `Take` needing
  *all* branches to spin. Monotonicity: `state_spin_mon`.
- `_of_itreeF` — one step of the behaviour relation, with a *coinductive*
  parameter `coself` (used only under `sb_interact`, i.e. after a visible
  event) and an *inductive* parameter `self`: `sb_final`, `sb_abort` (any tree
  admits `Tr.abort`), `sb_spin`, `sb_tau`, `sb_hang`, `sb_interact`,
  `sb_choose` (∃ a branch), `sb_take` (∀ branches). `_of_itree` ties the
  inductive knot and `Beh.of_itree := paco2 _of_itree bot2` the coinductive
  one — a mixed inductive/coinductive definition.
- `of_itree_tarski` (least-fixed-point principle for the inner induction),
  `of_itree_mon`, and the combined induction principle `of_itree_ind`.
- Paco/`core` hint databases for all of the above.

## `ConcRA.v` — resource algebra for concurrency

Ghost state for thread identity and yielding.

- `concGpreS`: `inG (excl_authUR natO)` for the current thread id, and
  `inG (nat -d> optionUR (exclR unitO))` for per-thread yield tokens.
  `concGS` adds the two ghost names `tid_name`, `yield_name`.
  `concΓ` / `concΣ` are the corresponding functor lists, with `subG_concG`.
- `crisG Γ Σ α β τ _S _I` bundles `cris_coreG` (from
  [`iris_system`](../iris_system/)) with `concGS`; projections `crisG_core`,
  `crisG_conc`.
- Predicates: `TidToken tid` (`◯E tid`), `TidTokenAuth tid` (`●E tid`),
  `YieldToken tid` (the singleton discrete function at `tid`),
  `YieldTokenAuth nths` (all tokens `≥ nths`), with notations
  `TID`, `TIDAUTH`, `YIELD`, `YIELDAUTH`.
- Laws: `TidToken_agree`, `TidToken_both` (two tokens are contradictory),
  `TidToken_upd`, `YieldToken_both` (distinctness), `YieldToken_gen` (carve a
  fresh yield token out of the authority, bumping the thread count).
- `cris_alloc` — the initial-resource allocation lemma: produces an `invGS`,
  an interpretation `β`, a `TypG.t`, a `crisG`, the world invariant
  `winv (⊤,⊤)`, and the initial `TID 0`, `YIELD 0`, `TIDAUTH 0`,
  `YIELDAUTH 1`.

## `Fn.v` — function names

`Variant fname := funid (fn : string) | entry`, i.e. an ordinary function or
the distinguished program entry point; notation `fid fs := funid fs.1`.
`EqDecision` and `Countable` instances (via `inj_countable'` into
`option string`). `fname_to_option`, `get_fids : gset fname -> gset string`,
and `maxlen_get_fids_union` (used for fresh-name generation when composing
modules).

## `IRed.v` — the interpreter-reduction framework (`ired`)

Generic machinery for normalising *any* interpreter application
`interp … itr` by pushing the interpreter through the itree structure. Built
on top of the positional rewriter `prw` from
[`theories/lib/Red.v`](../lib/Red.v).

- Term-inspection tactics: `get_head`, `get_head2` (stop at the argument whose
  type mentions `ReSum`, so subevent coercions are not stripped), `get_itr`,
  `get_nth` (with a demonstration goal).
- `Variant Box := mk_box (A : Type) (a : A)` — a universe-polymorphic wrapper
  so that lemmas of different types can be stored in one record.
- **`Class red_database (interp : Box)`** — the registry. An instance supplies
  `rdb_pos` (which argument position holds the itree) and boxed reduction
  lemmas for every syntactic form: `rdb_bind`, `rdb_tau`, `rdb_ret`,
  `rdb_trigger0`–`rdb_trigger3` (one per event summand),
  `rdb_UB`, `rdb_NB`, `rdb_unwrapU`, `rdb_unwrapN`, `rdb_assume`,
  `rdb_guarantee`, and `rdb_ext` (congruence, used to recurse into a nested
  interpreter). Every interpreter defined in CRIS registers such an instance.
- Congruence lemmas `bind_ext`, `bind_extk`, `tau_ext`.
- The reduction strategies: `_red_itree` (pure monad-law steps),
  `__red_interp` / `_red_interp` (look up the `red_database` instance for the
  head interpreter, then apply the matching boxed lemma; special-cases
  `unwrapU`/`unwrapN` of `Any.downcast ∘ Any.upcast` and
  `Any.split ∘ Any.pair`), and the combined `_red_gen`, which is what callers
  pass to `prw`.
- A large commented-out `TEST` module showing how to register three stacked
  interpreters `x`, `y`, `z` (and a parameterised one, `xx`, with
  `rdb_pos = 1`) and normalise their compositions, plus a commented-out
  alternative design based on a `NTR.t` record of natural transformations.

## `Common.v` — the base prelude

Eight lines of `Require Export`: the standard library bits
(`Program`, `Permutation`, `Orders`, `String`, `HexString`, `ZArith`),
`CRIS.lib` (`StdAxioms`, `Any`, `AList`, `Red`, `SubPerm`, `sflib`, `Coqlib`,
`ITreelib`, `SAT`), `CRIS.common.IRed`, the Iris layer
(`own`, `invariants`, `sProp`, `syn_invariants`), and `Events` + `Behavior`.
Importing this gives the full base vocabulary.

## `CRIS.v` — the top-level prelude

What a client of the framework imports. Adds to `Common`: `ConcRA`, Iris's
proof mode, `Fn`, the module layer (`FSpec`, `Sp`, `SMod`, `Mod`), the
simulation layer (`ISim`, `ISimFacts`, `WSim`, `WSimFacts`, `SimNotations`,
`TacticsCommon`, `Tactics`, `TacticsInit`), the filters (`CallFilter`,
`SysFilter`), `IrisTactics`, the contextual-refinement layer (`CtxRefine`,
`CtxRefineFacts`, `ClosedAdequacy`, `MainAdequacy`), and the Iris algebras
(`auth`, `excl`, `excl_auth`, `functions`, `frac`, `agree`, `gmap`, `big_op`,
`coPset`, `namespaces`).