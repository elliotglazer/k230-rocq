(** An exact arithmetic run predicate for the public 230-state transition table.
    This defines a literal machine-halting sentence; its uniform equivalence
    to the six-register proof-search run is a separate theorem. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 SentenceBounds TM230BinaryStep.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature |0.
#[local] Existing Instance PA_preds_signature |0.
#[local] Existing Instance falsity_on |0.
Definition machine230_state_index M i j:=addM M(mulM M(code_numeral M 4)i)(code_numeral M j).
Definition machine230_index_term(i:term)(j:nat):term:=(num 4⊗i)⊕num j.
Definition machine230_state_at M b c i(s:machine230_config(carrier M)):Prop :=
 beta M b c(machine230_state_index M i 0)(machine230_state s) /\
 beta M b c(machine230_state_index M i 1)(machine230_left s) /\
 beta M b c(machine230_state_index M i 2)(machine230_head s) /\
 beta M b c(machine230_state_index M i 3)(machine230_right s).
Definition machine230_state_at_formula(b c i q l h r:term):form:=
 beta_formula b c(machine230_index_term i 0)q ∧
 (beta_formula b c(machine230_index_term i 1)l ∧
 (beta_formula b c(machine230_index_term i 2)h ∧
 beta_formula b c(machine230_index_term i 3)r)).
Lemma machine230_index_term_correct M rho i j:
 evalM M rho(machine230_index_term i j)=machine230_state_index M(evalM M rho i)j.
Proof. unfold machine230_index_term,machine230_state_index. rewrite machine230_eval_add,machine230_eval_mul,!code_eval_num. reflexivity. Qed.
Lemma machine230_state_at_formula_correct M rho b c i q l h r:
 holds M rho(machine230_state_at_formula b c i q l h r)<->
 machine230_state_at M(evalM M rho b)(evalM M rho c)(evalM M rho i)
 (machine230_mk_config(carrier M)(evalM M rho q)(evalM M rho l)(evalM M rho h)(evalM M rho r)).
Proof.
 unfold machine230_state_at_formula,machine230_state_at.
 rewrite !holds_and,!beta_formula_correct,!machine230_index_term_correct. reflexivity.
Qed.
Fixpoint machine230_lift(n:nat)(t:term):term:=match n with 0=>t|S k=>(machine230_lift k t)`[↑]end.
Lemma machine230_lift9_eval M rho a b c d e f g h i t:
 evalM M(i.:h.:g.:f.:e.:d.:c.:b.:a.:rho)(machine230_lift 9 t)=evalM M rho t.
Proof. unfold evalM;cbn[machine230_lift]. now rewrite !eval_up. Qed.
Definition machine230_transitions_formula(b c N:term):form:=
 ∀∀∀∀∀∀∀∀∀
 (Peano.sless $8(machine230_lift 9 N)→
 (machine230_state_at_formula(machine230_lift 9 b)(machine230_lift 9 c)$8 $7 $6 $5 $4→
 (machine230_state_at_formula(machine230_lift 9 b)(machine230_lift 9 c)(σ $8)$3 $2 $1 $0→
 machine230_step_formula $7 $6 $5 $4 $3 $2 $1 $0))).
Definition machine230_run M b c N:Prop:=
 machine230_state_at M b c(zeroM M)(machine230_seed M) /\
 forall i s t,coding_lt M i N->machine230_state_at M b c i s->
 machine230_state_at M b c(succM M i)t->machine230_step M s t.
Definition machine230_run_formula(b c N:term):form:=
 machine230_state_at_formula b c zero zero zero zero zero ∧machine230_transitions_formula b c N.
Local Opaque holds machine230_step_formula machine230_state_at_formula.
Lemma machine230_transitions_formula_correct M rho b c N:
 holds M rho(machine230_transitions_formula b c N)<->
 (forall i s t,coding_lt M i(evalM M rho N)->
  machine230_state_at M(evalM M rho b)(evalM M rho c)i s->
  machine230_state_at M(evalM M rho b)(evalM M rho c)(succM M i)t->machine230_step M s t).
Proof.
 unfold machine230_transitions_formula. repeat setoid_rewrite holds_all.
 repeat setoid_rewrite holds_imp. setoid_rewrite less_formula_correct.
 setoid_rewrite machine230_state_at_formula_correct.
 setoid_rewrite machine230_step_formula_correct.
 setoid_rewrite machine230_lift9_eval.
 split.
 -intros H i[q l h r][q' l' h' r']Hi Hs Ht. exact(H i q l h r q' l' h' r' Hi Hs Ht).
 -intros H i q l h r q' l' h' r' Hi Hs Ht.
  exact(H i(machine230_mk_config(carrier M)q l h r)(machine230_mk_config(carrier M)q' l' h' r')Hi Hs Ht).
Qed.
Theorem machine230_run_formula_correct M rho b c N:
 holds M rho(machine230_run_formula b c N)<->machine230_run M(evalM M rho b)(evalM M rho c)(evalM M rho N).
Proof.
 unfold machine230_run_formula,machine230_run. rewrite holds_and,machine230_state_at_formula_correct,machine230_transitions_formula_correct. reflexivity.
Qed.
Definition machine230_arithmetical_halts M:Prop:=
 exists b c N,machine230_run M b c N /\beta M b c(machine230_state_index M N 0)(code_numeral M 230).
Definition machine230_halt_sentence:form:=
 ∃∃∃(machine230_run_formula $2 $1 $0 ∧beta_formula $2 $1(machine230_index_term $0 0)(num 230)).
Theorem machine230_halt_sentence_correct M rho:
 holds M rho machine230_halt_sentence<->machine230_arithmetical_halts M.
Proof.
 unfold machine230_halt_sentence,machine230_arithmetical_halts.
 repeat setoid_rewrite holds_ex. setoid_rewrite holds_and.
 setoid_rewrite machine230_run_formula_correct. setoid_rewrite beta_formula_correct.
 setoid_rewrite machine230_index_term_correct. setoid_rewrite code_eval_num. reflexivity.
Qed.
Local Transparent machine230_step_formula machine230_state_at_formula.
Theorem machine230_halt_sentence_closed:closed machine230_halt_sentence.
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.
Print Assumptions machine230_run_formula_correct.
Print Assumptions machine230_halt_sentence_correct.
Print Assumptions machine230_halt_sentence_closed.
