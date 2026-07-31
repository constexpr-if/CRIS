# `library/helping` — the helping pattern

Logical path: `CRIS.helping`.

**Helping** is the concurrency idiom in which a thread that cannot make
progress on its own operation instead performs *someone else's* pending
operation. Verifying a helping data structure directly is notoriously hard;
CRIS's answer is to make helping *imaginary*.

The library provides two implementations of the same interface, `run` and
`help`, for a fixed "job" `jobcode`:

| Module | `run mn jobs` | `help mn jobs` |
| --- | --- | --- |
| **`HelpingOff`** | actually runs `jobcode` to completion | does nothing but yield |
| **`HelpingOn`** | *may* find its job already done and just take the result | runs *some* pending job on someone else's behalf |
| `HelpingDummy` | `triggerNB` | `triggerNB` |

The main theorem, `helping_onoff_correct`, says `HelpingOff ⊒ HelpingOn`
(composed with a filtered scheduler): a client that reasons as if every thread
does its own work is sound even when threads help each other. The client-facing
packaging is `HelpingFacts.helping_main` / `helping_main_filtered`.

`HelpPend`/`HelpDone` form a **resource-only protocol**: since the
`Unreleased` CHANGELOG entry there is no client-visible request state, and
`HelpingOn.try_run` takes only a request id.

---

## `HelpingHeader.v`

`Helping.run mn := "★" +:+ mn`, `Helping.help mn := "☆" +:+ mn`,
`Helping.exports mn := {[run; help]}`, and the protocol's state type

```coq
Variant help_state := Pend (N : option namespace) (arg : SAny.t)
                    | InProgress
                    | Done (ret : SAny.t).
```

## `HelpingResource.v` — the client-visible protocol

Ghost state: `helpingGpreS` needs
`inG (prodR (optionR coPset_disjUR) (optionR (gmap_viewR nat (agreeR (leibnizO help_state))))) Γ`
(a mask component, used by `hinv` in `HelpingTactics`, and a request map) plus
`inG (exclR unitO) Γ`; with `helpingΓ`, `subG_helpingpreS`, and `helpingGS`
(adding `help_name`).

Predicates, each with a syntactic mirror and an `SLRed` instance so they can
appear in invariants: `Help reqid df st` / `syn_Help`,
**`HelpPend reqid N arg`** (full ownership of a pending request) / `syn_HelpPend`,
**`HelpDone reqid ret`** (a *persistent*, discarded-fraction witness that the
request finished with `ret`) / `syn_HelpDone`.
`Help_persist` and `HelpDone_persistent`.

## `HelpingOff.v` / `HelpingOn.v` — the two implementations

**`HelpingOff`**: `run (N, arg)` iterates `jobcode` (sandboxed with
`msk_pure`), yielding under `𝒴@{N}` between iterations; `help N` just yields.
`HelpingOff.Mod` / `HelpingOff.t`.

**`HelpingOn`**:
- **`try_run mn jobcode reqid`** — angelically `Choose (option SAny.t)`. If
  `Some ret`, the job has already been done for us: just `Guarantee (HelpDone reqid ret)`
  and return. If `None`, we must do it ourselves: `Guarantee (HelpPend reqid N arg)`,
  run the job loop, `Assume (HelpDone reqid ret)`, return.
- `run (N, arg)` — `Take` a request id, `Assume (HelpPend reqid N arg)`, yield,
  then `try_run`.
- `help Nhelp` — `Choose` a request id, a namespace and an argument,
  `Guarantee (HelpPend reqid N jobarg)`, swap out of `Nhelp` and into `N`, run
  the job, swap back, `Assume (HelpDone reqid ret)`.
- `HelpingOn.Mod mn jobcode` / `HelpingOn.t`.

**`HelpingDummy`** — both functions are `triggerNB` (mask `msk_real`); it is
the module that `HelpingOn` replaces in the first refinement step.

## `HelpingOnOffResource.v` — the authority side

`Section protocol`: `HelpAuth reqmap`, `help_erasure_init_cond := HelpAuth ∅`,
and the protocol steps `HelpAuth_Help` (agreement), **`HelpAuth_issue`**
(allocate a fresh pending request), `HelpAuth_update`, **`HelpAuth_claim`**
(`Pend → InProgress`), **`HelpAuth_publish`** (`InProgress → Done`, making the
witness persistent), `HelpAuth_observe_done`.

`Section global_protocol`: `HelpRun reqmap` — the big separating conjunction
carrying the resources of all in-flight requests — and `res_rel reqmap rt rs`,
the relation between the target's and the source's global resources. Lemmas:
`HelpRun_empty`, `HelpRun_lookup_acc`, `HelpRun_lookup_in_progress`,
`HelpRun_delete`, `HelpRun_insert`, `HelpRun_claim`, `HelpRun_publish`;
`res_rel_init`, `res_rel_issue`, `res_rel_claim`, `res_rel_publish`,
`res_rel_observe`.

## `HelpingAux.v` / `HelpingOnOffAux.v` — `gsim` lemmas

Because the two implementations are compared *after* compilation (the proof is
a `gsim` proof over the whole scheduled program), these files provide the
per-construct step lemmas.

`HelpingAux.v`: `option_Assume_sred`, `option_Guarantee_sred`,
`gsim_option_Guarantee_both`, `gsim_option_Assume_both`, and
**`gsim_jobs_both`** — the two job loops run in lockstep.

`HelpingOnOffAux.v`: the same lemmas in a *view*-carrying form, where a private
proposition `Priv` is threaded through — `gsim_Guarantee_both_view`,
`gsim_Assume_both_view`, `gsim_AssumeRes_both_view`,
`gsim_option_Guarantee_both_view`, `gsim_option_Assume_both_view`,
`gsim_jobs_both_view`. This is what lets the helping protocol's authority
travel across the steps.

## `HelpingOnOffproof.v` — the correctness proof (3 700 lines)

Fixes `mn`, a scope mask `msk` and `jobs`, and compares

```coq
mod_src := HelpingOff.t mn jobs ★ CFilter.filter msk SchI.t
mod_tgt := HelpingOn.t  mn jobs ★ CFilter.filter msk SchI.t
```

- Bookkeeping: `wf_src`, `msk_ctx`, the compiled bodies `run_s`/`run_t`,
  `help_s`/`help_t`, `yield`, `inner_spawn`, `spawn`, `join`;
  `dom_helping_on` / `dom_helping_off`; and the twelve `prog_{s,t}_*` lookup
  lemmas plus `prog_s_prog_t` (the two programs agree away from `run`/`help`).
- **`requests`** — extract the list of outstanding requests from the
  scheduler's thread pool, with `requests_app`, `requests_in`,
  `requests_inr`, `requests_id`, `requests_fmap_snd`.
- **`reqmap_rel`** — the coupling invariant between that list and the ghost
  `reqmap`, with a long list of preservation lemmas: `reqmap_rel_id`,
  `_id_2`, `_inprogress_done`, `_Some`, `_Some_2`, `_pend_inprogress`,
  `_done_2`, `_pend`, `_done`, `_insert_false`, `_insert_false_2`,
  `_insert_true`, `_append`.
- `gsim_Yield_tgt`, `gsim_option_Assume_Guarantee_src`.
- **`helping_onoff_correct`** — the theorem.

## `HelpingFacts.v` — client-facing packaging

`help_init_cond` and the allocation lemma `help_alloc`;
`helping_on_wf`, `helping_dummy_wf`, `helping_exports_long`;
the internal composition lemma `helping_refines_internal`; and the two
user-level theorems:

- **`helping_main_filtered fns mM mA mI ctx jobs`** — added in the
  `Unreleased` CHANGELOG entry; the version that composes with an existing
  filtered context. Given (a) a refinement replacing `HelpingDummy` by
  `HelpingOn` in the *implementation* direction and (b) a refinement replacing
  `HelpingOff` by the abstraction `mA`, it concludes
  `refines (mI ★ CFilter.filter fns (SchI.t ★ ctx)) (mA ★ SchI.t ★ ctx)`.
- **`helping_main mM mA mI mE jobs`** — the unfiltered version, concluding
  `ctx_refines (mI ★ mE ★ SchI.t) (mA ★ mE ★ SchI.t)`.

`help_init_cond` is then `Opaque`.

## `HelpingTactics.v` — client-side reasoning

`Section resource`: `hinv_ownE E` (a mask token carried in the *first*
component of the helping RA) with its syntactic mirror, `hinv_ownE_exploit`,
`hinv_ownE_op`, `hinv_ownE_subset`.

Simulation rules for a client of `HelpingOn`: `wsim_helping_run`,
`wsim_helping_pend_try_run`, `wsim_HelpDone_try_run`, `wsim_helping_help`.

**`IstHelp Ist E`** — lift a state invariant so that it additionally owns the
helping mask `E`; `IstHelp_nested_equiv` (the nested-transport lemma added in
the `Unreleased` CHANGELOG entry).

**`hinv N γ P`** — a *helping-aware invariant*: an ordinary `inv` guarded by an
exclusive token `γ`, with a syntactic mirror, an `SLRed` instance,
`hinv_persistent`, `hinv_excl_alloc`, `hinv_alloc`, `hinv_acc`, and the
proof-mode instances `into_inv_hinv` / `into_acc_hinv` so that `iInv` works on
it.

`Section help`: `wsim_helping_help2`, `IstHelp_done`,
`wsim_helping_try_run`.
