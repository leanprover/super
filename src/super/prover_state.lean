/-
Copyright (c) 2017 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import .clause .lpo .cdcl_solver
open tactic functor monad expr native

namespace super

structure score :=
(priority : ℕ)
(in_sos : bool)
(cost : ℕ)
(age : ℕ)

namespace score
def prio.immediate : ℕ := 0
def prio.default   : ℕ := 1
def prio.never     : ℕ := 2

def sched_default (sc : score) : score := { sc with priority := prio.default }
def sched_now (sc : score) : score := { sc with priority := prio.immediate }

def inc_cost (sc : score) (n : ℕ) : score := { sc with cost := sc.cost + n }

def min (a b : score) : score :=
{ priority := min a.priority b.priority,
  in_sos := a.in_sos && b.in_sos,
  cost := min a.cost b.cost,
  age := min a.age b.age }

def combine (a b : score) : score :=
{ priority := max a.priority b.priority,
  in_sos := a.in_sos && b.in_sos,
  cost := a.cost + b.cost,
  age := max a.age b.age }
end score

namespace score
meta instance : has_to_string score :=
⟨λe, "[" ++ to_string e.priority ++
     "," ++ to_string e.cost ++
     "," ++ to_string e.age ++
     ",sos=" ++ to_string e.in_sos ++ "]"⟩
end score

def clause_id := ℕ
namespace clause_id
def to_nat (id : clause_id) : ℕ := id
instance : decidable_eq clause_id := nat.decidable_eq
instance : has_lt clause_id := nat.has_lt
instance : decidable_rel ((<) : clause_id → clause_id → Prop) := nat.decidable_lt

end clause_id

meta structure derived_clause :=
(id : clause_id)
(c : clause)
(selected : list ℕ)
(assertions : list expr)
(sc : score)

namespace derived_clause

meta instance : has_to_tactic_format derived_clause :=
⟨λc, do
prf_fmt ← pp c.c.proof,
c_fmt ← pp c.c,
ass_fmt ← pp (c.assertions.map (λa, a.local_type)),
return $
to_string c.sc ++ " " ++
prf_fmt ++ " " ++
c_fmt ++ " <- " ++ ass_fmt ++
" (selected: " ++ to_fmt c.selected ++
")"
⟩

meta def clause_with_assertions (ac : derived_clause) : clause :=
ac.c.close_constn ac.assertions

meta def update_proof (dc : derived_clause) (p : expr) : derived_clause :=
{ dc with c := { (dc.c) with proof := p } }

end derived_clause

meta structure locked_clause :=
(dc : derived_clause)
(reasons : list (list expr))

namespace locked_clause

meta instance : has_to_tactic_format locked_clause :=
⟨λc, do
c_fmt ← pp c.dc,
reasons_fmt ← pp (c.reasons.map (λr, r.map (λa, a.local_type))),
return $ c_fmt ++ " (locked in case of: " ++ reasons_fmt ++ ")"
⟩

end locked_clause

meta structure prover_state :=
(active : rb_map clause_id derived_clause)
(passive : rb_map clause_id derived_clause)
(newly_derived : list derived_clause)
(prec : list expr)
(locked : list locked_clause)
(local_false : expr)
(sat_solver : cdcl.state)
(current_model : rb_map expr bool)
(sat_hyps : rb_map expr (expr × expr))
(needs_sat_run : bool)
(clause_counter : nat)

open prover_state

private meta def join_with_nl : list format → format :=
list.foldl (λx y, x ++ format.line ++ y) format.nil

private meta def prover_state_tactic_fmt (s : prover_state) : tactic format := do
active_fmts ← mapm pp $ rb_map.values s.active,
passive_fmts ← mapm pp $ rb_map.values s.passive,
new_fmts ← mapm pp s.newly_derived,
locked_fmts ← mapm pp s.locked,
sat_fmts ← mapm pp s.sat_solver.clauses,
sat_model_fmts ← s.current_model.to_list.mmap (λx, if x.2 = tt then pp x.1 else pp `(not %%x.1)),
prec_fmts ← mapm pp s.prec,
return (join_with_nl
  ([to_fmt "active:"]      ++ ((append (to_fmt "  ")) <$> active_fmts) ++
  [to_fmt "passive:"]      ++ ((append (to_fmt "  ")) <$> passive_fmts) ++
  [to_fmt "new:"]          ++ ((append (to_fmt "  ")) <$> new_fmts) ++
  [to_fmt "locked:"]       ++ ((append (to_fmt "  ")) <$> locked_fmts) ++
  [to_fmt "sat formulas:"] ++ ((append (to_fmt "  ")) <$> sat_fmts) ++
  [to_fmt "sat model:"]    ++ ((append (to_fmt "  ")) <$> sat_model_fmts) ++
  [to_fmt "precedence order: " ++ to_fmt prec_fmts]))

meta instance : has_to_tactic_format prover_state :=
⟨prover_state_tactic_fmt⟩

meta def prover := state_t prover_state tactic

namespace prover
local attribute [reducible] prover cdcl.solver

meta instance : monad prover := infer_instance
meta instance : alternative prover := infer_instance
meta instance : monad_state _ prover := infer_instance
meta instance : monad_state_adapter _ _ cdcl.solver prover := infer_instance
meta instance : has_monad_lift tactic prover := infer_instance
meta instance (α : Type) : has_coe (tactic α) (prover α) :=
⟨monad_lift⟩

end prover

meta def selection_strategy := derived_clause → prover derived_clause

meta def get_active : prover (rb_map clause_id derived_clause) :=
do state ← get, return state.active

meta def add_active (a : derived_clause) : prover punit :=
do state ← get,
put { state with active := state.active.insert a.id a }

meta def get_passive : prover (rb_map clause_id derived_clause) :=
passive <$> get

meta def get_precedence : prover (list expr) :=
do state ← get, return state.prec

meta def get_term_order : prover (expr → expr → bool) := do
state ← get,
return $ mk_lpo (name_of_funsym <$> state.prec)

private meta def set_precedence (new_prec : list expr) : prover punit :=
do state ← get, put { state with prec := new_prec }

meta def register_consts_in_precedence (consts : list expr) := do
p ← get_precedence,
p_set ← return (rb_map.set_of_list (name_of_funsym <$> p)),
new_syms ← return $ list.filter (λc, ¬p_set.contains (name_of_funsym c)) consts,
set_precedence (new_syms ++ p)

meta def in_sat_solver {A} : cdcl.solver A → prover A :=
adapt_state (λ st, (st.sat_solver, st)) (λ sat st, { sat_solver := sat, ..st })

meta def collect_ass_hyps (c : clause) : prover (list expr) :=
let lcs := contained_lconsts c.proof in
do st ← get,
return (do
  hs ← st.sat_hyps.values,
  h ← [hs.1, hs.2],
  guard $ lcs.contains h.local_uniq_name,
  [h])

meta def get_clause_count : prover ℕ :=
do s ← get, return s.clause_counter

meta def get_new_cls_id : prover clause_id := do
state ← get,
put { state with clause_counter := state.clause_counter + 1 },
return state.clause_counter

meta def mk_derived (c : clause) (sc : score) : prover derived_clause := do
ass ← collect_ass_hyps c,
id ← get_new_cls_id,
return { id := id, c := c, selected := [], assertions := ass, sc := sc }

meta def add_inferred (c : derived_clause) : prover unit := do
c' ← c.c.normalize, c' ← return { c with c := c' },
register_consts_in_precedence (contained_funsyms c'.c.type).values,
state ← get,
put { state with newly_derived := c' :: state.newly_derived },
skip



-- FIXME: what if we've seen the variable before, but with a weaker score?
meta def mk_sat_var (v : expr) (suggested_ph : bool) (suggested_ev : score) : prover unit :=
do st ← get, if st.sat_hyps.contains v then return () else do
hpv ← mk_local_def `h v,
hnv ← mk_local_def `hn $ imp v st.local_false,
modify $ λst, { st with sat_hyps := st.sat_hyps.insert v (hpv, hnv) },
in_sat_solver $ cdcl.mk_var_core v suggested_ph,
match v with
| (pi _ _ _ _) := do
  c ← clause.of_proof st.local_false hpv,
  mk_derived c suggested_ev >>= add_inferred
| _ := do cp ← clause.of_proof st.local_false hpv, mk_derived cp suggested_ev >>= add_inferred,
          cn ← clause.of_proof st.local_false hnv, mk_derived cn suggested_ev >>= add_inferred
end

meta def get_sat_hyp_core (v : expr) (ph : bool) : prover (option expr) :=
flip (<$>) get $ λst,
  match st.sat_hyps.find v with
  | some (hp, hn) := some $ if ph then hp else hn
  | none := none
  end

meta def get_sat_hyp (v : expr) (ph : bool) : prover expr :=
do hyp_opt ← get_sat_hyp_core v ph,
match hyp_opt with
| some hyp := return hyp
| none := fail $ "unknown sat variable: " ++ v.to_string
end

meta def add_sat_clause (c : clause) (suggested_ev : score) : prover unit := do
c ← c.distinct,
already_added ← flip (<$>) get $ λst, decidable.to_bool $
                     c.type ∈ st.sat_solver.clauses.map (λd, d.type),
if already_added then return () else do
c.get_lits.mmap' $ λl, mk_sat_var l.formula l.is_neg suggested_ev,
in_sat_solver $ cdcl.mk_clause c,
modify $ λst, { st with needs_sat_run := tt },
skip

meta def sat_eval_lit (v : expr) (pol : bool) : prover bool :=
do v_st ← flip (<$>) get $ λst, st.current_model.find v,
match v_st with
| some ph := return $ if pol then ph else bnot ph
| none := return tt
end

meta def sat_eval_assertion (assertion : expr) : prover bool :=
do lf ← flip (<$>) get $ λst, st.local_false,
match is_local_not lf assertion.local_type with
| some v := sat_eval_lit v ff
| none := sat_eval_lit assertion.local_type tt
end

meta def sat_eval_assertions : list expr → prover bool
| (a::ass) := do v_a ← sat_eval_assertion a,
if v_a then
sat_eval_assertions ass
else
return ff
| [] := return tt

private meta def intern_clause (c : derived_clause) : prover derived_clause := do
hyp_name ← get_unused_name (mk_simple_name $ "clause_" ++ to_string c.id.to_nat) none,
c' ← return $ c.c.close_constn c.assertions,
assertv hyp_name c'.type c'.proof,
proof' ← get_local hyp_name,
type ← infer_type proof', -- FIXME: otherwise ""
return $ c.update_proof $ app_of_list proof' c.assertions

meta def register_as_passive (c : derived_clause) : prover unit := do
c ← intern_clause c,
ass_v ← sat_eval_assertions c.assertions,
if c.c.num_quants = 0 ∧ c.c.num_lits = 0 then
  add_sat_clause c.clause_with_assertions c.sc
else if ¬ass_v then do
  modify $ λst, { st with locked := ⟨c, []⟩ :: st.locked }, skip
else do
  modify $ λst, { st with passive := st.passive.insert c.id c }, skip

meta def remove_passive (id : clause_id) : prover unit :=
do state ← get, put { state with passive := state.passive.erase id }, skip

meta def move_locked_to_passive : prover unit := do
locked ← flip (<$>) get (λst, st.locked),
new_locked ← flip filter locked (λlc, do
  reason_vals ← mapm sat_eval_assertions lc.reasons,
  c_val ← sat_eval_assertions lc.dc.assertions,
  if reason_vals.for_all (λr, r = ff) ∧ c_val then do
    modify $ λst, { st with passive := st.passive.insert lc.dc.id lc.dc },
    return ff
  else
    return tt
),
modify $ λst, { st with locked := new_locked }, skip

meta def move_active_to_locked : prover unit :=
do active ← get_active, active.values.mmap' $ λac, do
  c_val ← sat_eval_assertions ac.assertions,
  if ¬c_val then do
     modify $ λst, { st with
       active := st.active.erase ac.id,
       locked := ⟨ac, []⟩ :: st.locked
     }, skip
  else
    return ()

meta def move_passive_to_locked : prover unit :=
do passive ← flip (<$>) get $ λst, st.passive, passive.to_list.mmap' $ λpc, do
  c_val ← sat_eval_assertions pc.2.assertions,
  if ¬c_val then do
    modify $ λst, { st with
      passive := st.passive.erase pc.1,
      locked := ⟨pc.2, []⟩ :: st.locked
    }, skip
  else
    return ()

def super_cc_config : cc_config :=
{ em := ff }

meta def do_sat_run : prover (option expr) :=
do sat_result ← in_sat_solver $ cdcl.run (cdcl.theory_solver_of_tactic failure),
modify $ λst, { st with needs_sat_run := ff },
old_model ← prover_state.current_model <$> get,
match sat_result with
| (cdcl.result.unsat proof) := return (some proof)
| (cdcl.result.sat new_model) := do
    modify $ λst, { st with current_model := new_model },
    move_locked_to_passive,
    move_active_to_locked,
    move_passive_to_locked,
    return none
end

meta def take_newly_derived : prover (list derived_clause) := do
state ← get,
put { state with newly_derived := [] },
return state.newly_derived

meta def remove_redundant (id : clause_id) (parents : list derived_clause) : prover unit := do
when (not $ parents.for_all $ λp, p.id ≠ id) (fail "clause is redundant because of itself"),
red ← flip (<$>) get (λst, st.active.find id),
match red with
| none := return ()
| some red := do
let reasons := parents.map (λp, p.assertions),
let assertion := red.assertions,
if reasons.for_all $ λr, r.subset_of assertion then do
  modify $ λst, { st with active := st.active.erase id }, skip
else do
  modify $ λst, { st with active := st.active.erase id,
                                 locked := ⟨red, reasons⟩ :: st.locked }, skip
end

meta def inference := derived_clause → prover unit
meta structure inf_decl := (prio : ℕ) (inf : inference)
@[user_attribute]
meta def inf_attr : user_attribute :=
{name := `super.inf, descr := "inference for the super prover"}

meta def seq_inferences : list inference → inference
| [] := λgiven, return ()
| (inf::infs) := λgiven, do
    inf given,
    now_active ← get_active,
    if rb_map.contains now_active given.id then
      seq_inferences infs given
    else
      return ()

meta def simp_inference (simpl : derived_clause → prover (option clause)) : inference :=
λgiven, do maybe_simpld ← simpl given,
match maybe_simpld with
| some simpld := do
  derived_simpld ← mk_derived simpld given.sc.sched_now,
  add_inferred derived_simpld,
  remove_redundant given.id []
| none := return ()
end

meta def preprocessing_rule (f : list derived_clause → prover (list derived_clause)) : prover unit := do
state ← get,
newly_derived' ← f state.newly_derived,
state' ← get,
put { state' with newly_derived := newly_derived' }, skip

meta def clause_selection_strategy := ℕ → prover clause_id

namespace prover_state

meta def empty (local_false : expr) : prover_state :=
{ active := rb_map.mk _ _, passive := rb_map.mk _ _,
  newly_derived := [], prec := [], clause_counter := 0,
  local_false := local_false,
  locked := [], sat_solver := cdcl.state.initial local_false,
  current_model := rb_map.mk _ _, sat_hyps := rb_map.mk _ _, needs_sat_run := ff }

meta def initial (local_false : expr) (clauses : list clause) : tactic prover_state := do
after_setup ← (clauses.mmap' (λc : clause,
  let in_sos := ((contained_lconsts c.proof).erase local_false.local_uniq_name).size = 0 in
  do mk_derived c { priority := score.prio.immediate, in_sos := in_sos,
                    age := 0, cost := 0 } >>= add_inferred
)).run (empty local_false),
return after_setup.2

end prover_state

meta def inf_score (add_cost : ℕ) (scores : list score) : prover score := do
age ← get_clause_count,
return $ list.foldl score.combine { priority := score.prio.default,
                                    in_sos := tt,
                                    age := age,
                                    cost := add_cost
                                  } scores

meta def inf_if_successful (add_cost : ℕ) (parent : derived_clause) (tac : tactic (list clause)) : prover unit :=
(do inferred ← tac,
    inferred.mmap' $ λc,
      inf_score add_cost [parent.sc] >>= mk_derived c >>= add_inferred)
<|> return ()

meta def simp_if_successful (parent : derived_clause) (tac : tactic (list clause)) : prover unit :=
(do inferred ← tac,
    inferred.mmap' $ λc,
      mk_derived c parent.sc.sched_now >>= add_inferred,
    remove_redundant parent.id [])
<|> return ()

end super
