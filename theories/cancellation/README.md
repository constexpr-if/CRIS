# `theories/cancellation` — erasing specifications ("cancellation")

Logical path: `CRIS.cancellation`.

This directory proves the theorem that makes CRIS's *imaginary specifications*
sound: once every function of a module has been verified against its spec, all
the specification scaffolding — the `Take`/`Choose` of the `FSpec` record, the
`Assume`/`Guarantee` obligations, the whole Hoare wrapper — may be **cancelled**,
leaving a module with no specification at all.

```coq
Theorem Cancel.cancel M P Q :
  SMod.cancellable M →
  fspec_flat ((SMod.sp_from M).1 !! entry) P Q →
  (∀ varg arg, Q varg arg ⊢ ⌜varg = arg⌝) →
  P tt↑ tt↑ ∗ TIDAUTH 0 ∗ YIELDAUTH 1
    ⊢ refines (SMod.to_mod_cancel (SMod.sp_from M) M)   (* with specs *)
              (SMod.to_mod ∅ (SMod.cancel M))           (* without    *)
```

The proof route is:

```
SMod.to_mod_cancel sp M          (specified)
  ⊒ inline (SMod.to_mod_cancel sp M)      -- MInlineIntro.inline_intro
  ⊒ inline (SMod.to_mod ∅ (SMod.cancel M))-- Cancel.cancel_main  (a gsim proof)
  ⊒ SMod.to_mod ∅ (SMod.cancel M)         -- MInlineElim.inline_elim
```

The middle step is the hard one, and it is why the module must first be
**inlined**: after inlining there are no `Call` events left, so the erasure of
the Hoare wrapper is a purely local, per-thread argument.

---

## Inlining

### `MInline.v`

- `handle_callE prog itr` — one step of the inliner: a `Call fn args` is
  replaced by `prog fn args` followed by a `Tau`; `Spawn`, `Yield`, `GetTid`
  and all other events are re-emitted unchanged.
- `sandboxed_prog ms fn arg` — look the function up in `ms` and run its
  sandboxed body (undefined behaviour if absent).
- `inline_body prog := ITree.iter (handle_callE prog)`,
  `inline_fsem ms kb` — the inlined body, with the mask widened to
  `msk_scp (Mod.scopes ms) msk_true` (only the scope restriction survives).
- **`MInline.inline ms : Mod.t`** — apply `inline_fsem` to every function.
- `Module MIRed` — reduction lemmas for `inline_body`: `ret`, `tau`, `bind`,
  `spawn`, `yield`, `gettid`, `core`, `pg`, `ag`, `call`.
- `sandbox_inline_commute` — sandboxing and inlining commute.

### `MInlineIntro.v` / `MInlineElim.v`

`inline_intro : ⊢ refines md (MInline.inline md)` and
`inline_elim : ⊢ refines (MInline.inline md) md` — inlining is a refinement in
both directions. Both are proved with `ISim_closed_adequacy` after
generalising over all function bodies at once.

## `ElimRel.v` — the relation being maintained

The heart of the development: a *syntactic* relation between an unspecified
source tree and a specified target tree, which is preserved by every step and
which the `Cancel*` files discharge one event at a time.

**Erased Hoare wrappers.** `HoareSpawnE`, `HoareYieldE`, `HoareGetTidE` — the
concurrency wrappers of `SModTr` with the spec parts made optional;
`elim_precond`, `elim_postcond`, `elim_spawnee_precond`,
`elim_spawnee_postcond` — the pre/post fragments as standalone trees.

**`elim_rel_def` / `elim_rel`** (a `paco4`) — the per-thread relation. Cases:
`elim_take_false` / `elim_tau_take_false` / `elim_choose_false` (vacuous
sides), `elim_rel_ret`, `elim_rel_tau`, `elim_rel_core`, `elim_rel_pg`,
`elim_rel_ag`, then the *cancellation* cases `elim_rel_yield`,
`elim_rel_spawn`, **`elim_rel_precond`** (every source pre/post pair is
implied by some target pair, up to `|==>`), **`elim_rel_postcond`** (dually,
with `None` interpreted as the equality spec), and `elim_rel_gettid`.
With `elim_rel_def_mon`, the up-to-bind closure `elim_rel_bindC` /
`elim_rel_bindC_mon` / `elim_rel_bindC_spec`.

**Reduction lemmas** for pushing the sandbox and the inliner through the Hoare
wrappers: `SBRed_HoareSpawn`, `MIRed_HoareSpawn`, `SBRed_HoareYield`,
`MIRed_HoareYield`, `SBRed_HoareGetTid`, `MIRed_HoareGetTid`, `if_simpl`,
`MIRed_HoareFun`, `MIRed_HoareFun_cancel`.

**`Section CancelDef`.**
- **`thread_rel sp cid tid r_diff src tgt`** — the whole-thread relation, with
  three cases: `thread_rel_body` (the currently running thread — related by
  `elim_rel`), `thread_rel_spawn` (a thread that has been spawned but not yet
  scheduled — its precondition is still owed), and `thread_rel_yield` (a
  thread parked at a `Yield` — it will `Assume` its tokens when resumed).
  `r_diff` is the resource that thread owns.
- `cancel_eq` — the return relation: equal key-value states and equal return
  values, with possibly different resources.
- **`CANCEL_GOAL md sp R it_src it_tgt`** — the *proof obligation format*.
  It bundles everything a per-event lemma may assume: the thread pool
  (`srcs`, `tgts`, `rs_diff`) is `Forall3i (thread_rel …)`-related, the
  resource splits into the per-thread pieces plus `TIDAUTH`/`YIELDAUTH`, the
  coinduction hypothesis `CIH`, the "take one scheduling step" continuation
  `KEY`, and the current thread's head event. Each `Cancel*.v` file proves one
  instance of this format.
- Helper library `Forall3i`, `Forall3i_nth`, `list_lookup_length`.

## The per-event obligations

Each of these proves `CANCEL_GOAL md sp` for one class of head event:

| File | Lemma | Event |
| --- | --- | --- |
| `CancelCore.v` | `cancel_core` | `coreE` (`Choose`, `Take`, `IO`) |
| `CancelPG.v` | `cancel_pg` | `pgE` (`SPut`, `SGet`) |
| `CancelAG.v` | `cancel_ag` | `agE` (`Assume`, `AssumeRes`, `Guarantee`) |
| `CancelSpawn.v` | `cancel_spawn` | `Spawn fn args` |
| `CancelYield.v` | `cancel_yield` | `Yield ntid` (also proves `list_lookup_exists`) |
| `CancelGetTid.v` | `cancel_gettid` | `GetTid` |
| `CancelPre.v` | `cancel_pre` | the precondition block of `HoareFun` |
| `CancelPost.v` | `cancel_post` | the postcondition block of `HoareFun` |

`CancelSpawn` and `CancelYield` are the interesting ones: spawning must *hand
over* the callee's precondition together with its `YIELD`/`TID` tokens, and
yielding must give up the `winv (⊤,⊤)` bundle and re-`Assume` it on resumption.

## `Cancel.v` — assembling the theorem

- **`cancel_elim`** — the main coinduction. Given `SMod.cancellable md`, a
  thread pool related by `thread_rel`, and a resource splitting into the
  per-thread pieces plus `TIDAUTH cid` and `YIELDAUTH (length rs_diff)`, the
  two *scheduled* programs are `gsim cancel_eq`-related. The proof dispatches
  on the running thread's head event to the eight `cancel_*` lemmas above.
  Marked `(*SLOW*)`.
- **`cancel_main`** — specialise to the whole program: given that `entry`'s
  spec `(P, Q)` holds initially and that `Q` forces equal return values, the
  two compiled programs are `gsim eq smj_bot smj_bot`-related.
- **`Cancel.prepare`** : `⊢ ctx_refines (SMod.to_mod spt md) (SMod.to_mod_cancel sps md)` —
  the *first* half of the workflow, moving from an arbitrary spec map `spt` to
  the module's own specs `sps`. The side conditions say that wherever the two
  spec maps disagree the corresponding `Call`/`Spawn` is masked out, that
  `sps` enables imaginary concurrency, and that if `spt` does not then the
  system events are masked out too.
- `init_res := TID 0 ∗ YIELD 0 ∗ winv (⊤,⊤) ∗ TIDAUTH 0 ∗ YIELDAUTH 1` — the
  resources a whole program starts with.
- **`Cancel.cancel`** — the theorem quoted at the top, assembled from
  `inline_intro`, `cancel_main` (through `gsim_mod_intro` and
  `gsim_closed_adequacy`) and `inline_elim`.
