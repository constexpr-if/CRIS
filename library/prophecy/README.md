# `library/prophecy` — prophecy variables

Logical path: `CRIS.prophecy`.

A **prophecy variable** lets a proof learn *now* something that will only be
observed *later*. In CRIS this is realised as a module with three operations —
`new`, `resolve`, `close` — whose implementation (`ProphecyI`) does absolutely
nothing, but whose abstraction (`ProphecyA`) hands out a `proph` resource
recording the prophesied value.

Soundness is *not* an ordinary refinement argument, because a prophecy's value
must be chosen consistently with the *whole future trace*. This directory
therefore develops its own trace theory:

- `ExtendedBehavior.v` — traces that additionally record prophecy resolutions
  (`ExTr.t`, an `ExCoU` coinductive), plus a special interpreter
  (`proph_trans`) that emits them;
- `SimGEx.v` — a simulation relation `simg_ex` indexed by such an extended
  trace, with its own adequacy theorem;
- `ProphecyIAproof.v` — the (1 660-line) proof that ties the two together;
- `ProphecyFacts.v` — the client-facing packaging.

---

## `ProphecyHeader.v`

- `Prophecy.ID := string * SAny.t` with `ID_dec`.
- `firstn rs n` — the first `n` observations of a sequence, most recent first;
  `consistent_until consistent obs_seq p` — every suffix is consistent.
- **`Structure Prophecy.t`** — a prophecy *theory*: a type of prophecies `Pro`,
  a type of observations `Obs`, a consistency predicate
  `consistent : list Obs → Pro → Prop`, a default observation, and the crucial
  **`coverage`** axiom-as-field: for *every* infinite observation sequence
  there exists a prophecy consistent with all of its prefixes.
  `prophecy_consistent_until` strengthens `coverage` to `consistent_until`.
- Signatures `Prophecy.new mn`, `Prophecy.resolve mn`, `Prophecy.close mn`
  and `Prophecy.exports mn`. (Every prophecy module is parameterised by a
  fresh name `mn`; `ProphecyFacts` picks it with `mname_long`.)

## `ProphecyRA.v` — the resource algebra

`ProphInst := {P : Prophecy.t & (P.(Pro) * list P.(Obs))}` (a prophecy together
with the observations resolved so far);
`ProphRA := Prophecy.ID -d> excl_authUR (sumO unitO ProphInstO)`.
Classes `prophGpreS`, `prophGS`, functor list `prophΓ`, `subG_prophG`.

- `dummy_proph`, `dummy_prophinst`.
- **`proph id v`** — exclusive ownership of prophecy `id` at instance `v`
  (with `syn_proph` and `proph_red`).
- **`free_id P`** — the set of prophecy ids satisfying `P` is still unused.
  `proph_free_id` (an owned id is not free), and the splitting theory
  `free_id_r_split`, `free_id_split_singleton`, `free_id_split`,
  `free_id_iff`, `free_id_incl`, `free_id_sep_or`, `free_id_sep_or_iff`,
  `free_id_sepL`.
- `proph_auth P map` — the authority; `proph_alloc`.

## `ProphecyStream.v` — the canonical prophecy theory

The most-used instance: a prophecy *is* an infinite stream of observations.

`obs_stream`, `lookup_obs_stream`, `stake_S`, `length_firstn`,
`list_stream_app_app`, `list_stream_app_stake`, `lookup_list_stream_app_r`;
**`stream_prophecy Obs`** — the `Prophecy.t` whose prophecies are `stream Obs`
and whose consistency is "the observations are a prefix of the stream"
(the `coverage` field is witnessed by the stream itself);
`stream_prophecy_consistent_head`, `list_stream_app_consume`.

`ProphResolveInst`, `stream_proph_inst`, `stream_proph_resolve_arg`,
`stream_proph_resolved_inst`, **`stream_proph id str`** (with `syn_stream_proph`),
and the protocol lemmas `stream_proph_new`, `stream_proph_resolve`,
`stream_proph_resolve_open`.

`Section ProphecyStreamWSim` gives the two client-facing simulation rules
`wsim_stream_proph_new` and `wsim_stream_proph_resolve`.

## `ProphecyI.v` / `ProphecyA.v` — the two modules

**`ProphecyI`** — `new`, `resolve` and `close` all return `tt↑`. No scopes, no
specs, mask `msk_real (msk_scp [] msk_true)`; `ProphecyI.real`.

**`ProphecyA`** — the same trivial bodies (`fbody_trivial`), but with specs:
- `new_spec` — consumes `free_id (.= id)`, produces `∃ p, proph id (existT P (p, nil))`;
- `resolve_spec` — consumes `proph id (existT P (p, obs_seq))` and the
  observation `obs`, produces `proph id (existT P (p, obs :: obs_seq))`
  *together with the pure fact* `consistent (obs :: obs_seq) p` — this is
  where the proof learns the future;
- `close_spec` — gives the id back to `free_id`.

`ProphecyA.initial_cond := proph_auth (Full_set _) (λ _, dummy_prophinst)`,
`ProphecyA.t sp`, and `filter_helping` (the module is unaffected by the
helping filter).

## `ExtendedBehavior.v` — traces with prophecy resolutions

- `prefix_io := "normal_"`, `prefix_proph := "prophecy_"` — resolutions are
  encoded as specially-prefixed `IO` events.
- `ths_state := nat * list (bool * itree lmodE Any.t)` — the thread pool, each
  thread flagged as "inside a prophecy call" or not — and
  `proph_handle_callE` / `proph_interp_callE` / **`proph_trans`** /
  `proph_compile`: a variant of `LModTr` that keeps prophecy resolutions
  visible instead of erasing them.
- **`Module ExTr`** — the extended trace type, built with `ExCoU` (the
  non-indexed coinductive container of
  [`theories/lib/exco.v`](../../theories/lib/exco.v)): operations `_done`,
  `_abort`, `_hang`, `_interact`, `_tau`, `_choose X x`, `_take P`, with the
  smart constructors `done`, `abort`, `hang`, `interact`, `tau`, `choose`,
  `take` and `unfold_extr`. Note that, unlike `Tr.t`, `ExTr.t` records the
  *witness* of every `Choose` and the *type* of every `Take`.
- **`Module ExBeh`** — `_of_itreeF` / `of_itree` (a `paco2`) assigning extended
  traces to an `itree coreE`, with `of_itree_mon` and `of_itree_ind`.
- `Section ETO` ("extended trace ↔ observation stream"):
  `extrace_obs_stream_relation` (with monotonicity), `eto_adeq_rel`,
  `et_spin`, `et_step`, `et_step_or_spin`, `eto_adeq_step`,
  **`adeq_rel_sound`**, and **`extrace_has_obs_stream`** — *every* extended
  trace induces an observation stream. Combined with `Prophecy.coverage`, this
  is what lets a consistent prophecy always be produced.
- `Section TREXTRREL` — `extr_spin` and the relation between ordinary `Tr.t`
  behaviours and extended ones.

## `SimGEx.v` — simulation indexed by an extended trace

`simg_ex_def` / `simg_ex` (a `paco5`): a simulation between two
`itree coreE Any.t` that additionally *consumes* an `ExTr.t`, so that the
prophecy resolutions in the trace can guide the source's angelic choices.
Metatheory `simg_ex_def_mon`, `simg_ex_tarski`, `simg_ex_mon`, `simg_ex_ind`;
per-constructor adequacy lemmas (`_ret`, `_hang`, `_interact_normal`,
`_spin`, `_interact_proph`, `_tau`, `_choose`, `_take`, each with an `_aux`);
and **`simg_ex_adequacy`**.

`wsimg` — a convenience wrapper — with the step rules `wsimg_tau_src`,
`wsimg_take_src`, `wsimg_choose_src`, `wsimg_tau_tgt`, `wsimg_choose_tgt`,
`wsimg_take_tgt`, `wsimg_io_normal`, `wsimg_io_proph`, `wsimg_ret`,
`wsimg_endsim`.

## `ProphecyIAproof.v` — soundness

The core argument, for an arbitrary *real* client module `md`:

- `take_is_prop` (a `paco1`) — every `Take` in the module is at a
  propositional type, i.e. the module is "real"; `take_is_prop_mon`,
  `take_is_prop_load`, `take_is_prop_bind`, `mod_take_is_prop`.
- `thread_rel` and `thread_rel_load` — relate a plain thread to a
  prophecy-flagged one.
- **`mod_proph_comp_sim`** — the module's compilation under `proph_trans`
  simulates its ordinary compilation.
- **`prophecy_tgt_exbeh_exists`** — the target program *has* an extended
  behaviour (so `extrace_has_obs_stream` applies).
- `wf_sim` (a `paco2`), `wf_sim_mon`, `thread_list_load_relation`,
  `wf_sim_bind`, `pmod_fun_wf_sim`.
- Small list/stream lemmas `firstn_reverse`, `firstn_length`,
  `stream_app_cons`; `consistent_sany` / `consistent_sany_equiv` (transporting
  consistency across the `SAny.t` boxing); `src_mod_wf`.
- **`adequacy_aux`** — the main induction (roughly 900 lines), carrying the
  prophecy map, the set of free ids, the extended trace, the thread pool on
  both sides and the prophecy store.
- `adequacy_refines_mod` and **`adequacy_refines`** — the packaged results.

## `ProphecyFacts.v` — client-facing packaging

`prophecy_exports_long` (the generated module name is longer than anything in
the client, hence fresh — this is what `Coqlib`'s `mname_long`/`maxlen`
machinery is for);
**`prophecy_refines sz mds mdt ctx`** — the workhorse; and
**`prophecy_main mds mdt ctx mdm`**:

```coq
(∀ mn, real_mod (mdm mn)) → real_mod ctx →
  (∀ mn, ctx_refines (CFilter.filter (Prophecy.exports mn) mdt ★ ProphecyI.t mn)
                     (mdm mn ★ ProphecyI.t mn))
  ∗ ProphecyA.initial_cond
  ∗ (∀ mn, ctx_refines (mdm mn ★ ProphecyA.t mn ∅) mds)
  ⊢ refines (mdt ★ ctx) (mds ★ ctx)
```

i.e. to refine `mdt` by `mds` you may go through an intermediate module `mdm`
that has prophecies available, discharging one side against the trivial
implementation `ProphecyI` and the other against the specified `ProphecyA`.
