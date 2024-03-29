/-
Copyright (c) 2017 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import .clause .prover_state
import .misc_preprocessing
import .selection
import .trim

-- default inferences
-- 0
import .clausifier
-- 10
import .demod
import .inhabited
import .datatypes
-- 20
import .subsumption
-- 30
import .splitting
-- 40
import .factoring
import .resolution
import .superposition
import .equality
import .simp
import .defs

open monad tactic expr

declare_trace super

namespace super

meta def trace_clauses : prover unit :=
do state ← get, trace state

meta def run_prover_loop
  (literal_selection : selection_strategy)
  (clause_selection : clause_selection_strategy)
  (preprocessing_rules : list (prover unit))
  (inference_rules : list inference)
  (max_iters : ℕ)
  : ℕ → prover (option expr) | i := do
sequence' preprocessing_rules,
new ← take_newly_derived, new.mmap' register_as_passive,
when (is_trace_enabled_for `super) $ new.mmap' $ λn,
  tactic.trace { n with c := { n.c with proof := const (mk_simple_name "derived") [] } },
needs_sat_run ← flip (<$>) get (λst, st.needs_sat_run),
if needs_sat_run then do
  res ← do_sat_run,
  match res with
  | some proof := return (some proof)
  | none := do
    model ← flip (<$>) get (λst, st.current_model),
      when (is_trace_enabled_for `super) (do
      pp_model ← pp (model.to_list.map (λlit, if lit.2 = tt then lit.1 else `(not %%lit.1))),
      trace $ to_fmt "sat model: " ++ pp_model),
    run_prover_loop i
  end
else do
passive ← get_passive,
if passive.size = 0 then return none else do
given_name ← clause_selection i,
given ← option.to_monad (passive.find given_name),
-- trace_clauses,
remove_passive given_name,
given ← literal_selection given,
  when (is_trace_enabled_for `super) (do
  fmt ← pp given, trace (to_fmt "given: " ++ fmt)),
add_active given,
seq_inferences inference_rules given,
when (i ≥ max_iters) $ fail "reached maximum number of iterations in saturation loop",
run_prover_loop (i+1)

meta def default_preprocessing : list (prover unit) :=
[
clausify_pre,
clause_normalize_pre,
factor_dup_lits_pre,
remove_duplicates_pre,
refl_r_pre,
diff_constr_eq_l_pre,
tautology_removal_pre,
subsumption_interreduction_pre,
forward_subsumption_pre,
return ()
]

end super

open super

meta structure super.opts :=
(max_iters : ℕ := 200)
(timeout : ℕ := 20000)

meta def super (sos_lemmas : list expr) (os : super.opts) : tactic unit := do
try_for os.timeout $ with_trim $ do
as_refutation, local_false ← target,
clauses ← clauses_of_context,
sos_clauses ← sos_lemmas.mmap (clause.of_proof local_false),
initial_state ← prover_state.initial local_false (clauses ++ sos_clauses),
inf_names ← attribute.get_instances `super.inf,
infs ← inf_names.mmap $ λn, eval_expr inf_decl (const n []),
infs ← return $ list.map inf_decl.inf $ list.sort_on inf_decl.prio infs,
res ← (run_prover_loop selection21 (age_weight_clause_selection 3 4)
  default_preprocessing infs
  os.max_iters 0).run initial_state,
match res with
| (some empty_clause, st) := apply empty_clause >> skip
| (none, saturation) := do sat_fmt ← pp saturation,
                           fail $ to_fmt "saturation:" ++ format.line ++ sat_fmt
end

namespace tactic.interactive
open lean.parser
open interactive
open interactive.types

meta def with_lemmas (ls : parse $ many ident) : tactic unit :=
ls.mmap' $ λ l, do
eqn_ls ← get_eqn_lemmas_for tt l <|> return [],
(l :: eqn_ls).mmap' $ λ l, do
p ← mk_const l,
t ← infer_type p,
n ← get_unused_name p.get_app_fn.const_name none,
tactic.assertv n t p

meta def super (extra_clause_names : parse $ many ident)
               (extra_lemma_names : parse with_ident_list)
               (opts : super.opts := {}) : tactic unit := do
with_lemmas extra_clause_names,
extra_lemmas ← extra_lemma_names.mmap (λ c, do
  eqn_ls ← get_eqn_lemmas_for tt c,
  (c::eqn_ls).mmap mk_const),
_root_.super extra_lemmas.join opts

end tactic.interactive
