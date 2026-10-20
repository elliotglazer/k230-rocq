(** The four literal quantifier rules of FullND, with de Bruijn shift
    and capture-avoiding outer-binder instantiation represented internally. *)
From PAModel Require Import Model FiniteCoding NumericalProofs CodeExpressions SourceSequents
  SourcePropositionalRules NumericalContexts NumericalEnvironments
  NumericalContextRenaming NumericalRenaming NumericalInstantiation SetFormulaCodes
  NumericalTraces SentenceBounds.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_formula_shift M f g :=
  numerical_renaming M f (zeroM M) (zeroM M) (zeroM M) (succM M (zeroM M)) g.
Definition source_formula_shift_formula (f g : term) : form :=
  numerical_renaming_formula f zero zero zero (σ zero) g.
Lemma source_formula_shift_formula_correct M rho f g :
  holds M rho (source_formula_shift_formula f g) <->
  source_formula_shift M (evalM M rho f) (evalM M rho g).
Proof. apply numerical_renaming_formula_correct. Qed.

Local Opaque holds source_sequent_formula source_branches_formula sf_formula
  environment_cons_formula context_shift_formula numerical_instantiation_formula
  source_formula_shift_formula source_row_wf_formula.
Definition source_case_AllI M r p := exists b c n a f u v,
  ((source_sequent M b c n f r) /\ ((source_sequent M u v n a p) /\ ((context_shift M b c n u v) /\ (sf_relation M SFAll a (zeroM M) f)))).
Definition source_case_AllI_formula : form := ∃∃∃∃∃∃∃
  ((source_sequent_formula $6 $5 $4 $2 $7) ∧ ((source_sequent_formula $1 $0 $4 $3 $8) ∧ ((context_shift_formula $6 $5 $4 $1 $0) ∧ (sf_formula SFAll $3 zero $2)))).
Lemma source_case_AllI_correct M rho r p :
  holds M (r .: p .: rho) source_case_AllI_formula <-> source_case_AllI M r p.
Proof.
  unfold source_case_AllI_formula,source_case_AllI.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite source_sequent_formula_correct.
  setoid_rewrite context_shift_formula_correct.
  setoid_rewrite sf_formula_correct.
  reflexivity.
Qed.

Definition source_case_AllE M r p := exists b c n a f t g,
  ((source_sequent M b c n g r) /\ ((source_sequent M b c n f p) /\ ((sf_relation M SFAll a (zeroM M) f) /\ (numerical_instantiation M a t g)))).
Definition source_case_AllE_formula : form := ∃∃∃∃∃∃∃
  ((source_sequent_formula $6 $5 $4 $0 $7) ∧ ((source_sequent_formula $6 $5 $4 $2 $8) ∧ ((sf_formula SFAll $3 zero $2) ∧ (numerical_instantiation_formula $3 $1 $0)))).
Lemma source_case_AllE_correct M rho r p :
  holds M (r .: p .: rho) source_case_AllE_formula <-> source_case_AllE M r p.
Proof.
  unfold source_case_AllE_formula,source_case_AllE.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite source_sequent_formula_correct.
  setoid_rewrite sf_formula_correct.
  setoid_rewrite numerical_instantiation_formula_correct.
  reflexivity.
Qed.

Definition source_case_ExI M r p := exists b c n a f t g,
  ((source_sequent M b c n f r) /\ ((source_sequent M b c n g p) /\ ((sf_relation M SFEx a (zeroM M) f) /\ (numerical_instantiation M a t g)))).
Definition source_case_ExI_formula : form := ∃∃∃∃∃∃∃
  ((source_sequent_formula $6 $5 $4 $2 $7) ∧ ((source_sequent_formula $6 $5 $4 $0 $8) ∧ ((sf_formula SFEx $3 zero $2) ∧ (numerical_instantiation_formula $3 $1 $0)))).
Lemma source_case_ExI_correct M rho r p :
  holds M (r .: p .: rho) source_case_ExI_formula <-> source_case_ExI M r p.
Proof.
  unfold source_case_ExI_formula,source_case_ExI.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite source_sequent_formula_correct.
  setoid_rewrite sf_formula_correct.
  setoid_rewrite numerical_instantiation_formula_correct.
  reflexivity.
Qed.

Definition source_case_ExE M r p q := exists b c n a ex f g u v x y l,
  ((source_sequent M b c n f r) /\ ((source_sequent M b c n ex p) /\ ((source_sequent M x y l g q) /\ ((sf_relation M SFEx a (zeroM M) ex) /\ ((context_shift M b c n u v) /\ ((environment_cons M u v n a x y l) /\ (source_formula_shift M f g))))))).
Definition source_case_ExE_formula : form := ∃∃∃∃∃∃∃∃∃∃∃∃
  ((source_sequent_formula $11 $10 $9 $6 $12) ∧ ((source_sequent_formula $11 $10 $9 $7 $13) ∧ ((source_sequent_formula $2 $1 $0 $5 $14) ∧ ((sf_formula SFEx $8 zero $7) ∧ ((context_shift_formula $11 $10 $9 $4 $3) ∧ ((environment_cons_formula $4 $3 $9 $8 $2 $1 $0) ∧ (source_formula_shift_formula $6 $5))))))).
Lemma source_case_ExE_correct M rho r p q :
  holds M (r .: p .: q .: rho) source_case_ExE_formula <-> source_case_ExE M r p q.
Proof.
  unfold source_case_ExE_formula,source_case_ExE.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite source_sequent_formula_correct.
  setoid_rewrite sf_formula_correct.
  setoid_rewrite context_shift_formula_correct.
  setoid_rewrite environment_cons_formula_correct.
  setoid_rewrite source_formula_shift_formula_correct.
  reflexivity.
Qed.

Definition source_full_unary M r p := source_prop_unary M r p \/
  (source_row_wf M r /\ (source_case_AllI M r p \/ (source_case_AllE M r p \/ source_case_ExI M r p))).
Definition source_full_unary_formula : form := source_prop_unary_formula ∨
  (source_row_wf_formula $0 ∧ (source_case_AllI_formula ∨ (source_case_AllE_formula ∨ source_case_ExI_formula))).
Lemma source_full_unary_correct M rho r p :
  holds M (r .: p .: rho) source_full_unary_formula <-> source_full_unary M r p.
Proof.
  unfold source_full_unary_formula,source_full_unary.
  rewrite holds_or, source_prop_unary_correct, holds_and. repeat setoid_rewrite holds_or.
  rewrite source_row_wf_formula_correct.
  rewrite source_case_AllI_correct.
  rewrite source_case_AllE_correct.
  rewrite source_case_ExI_correct.
  reflexivity.
Qed.
Lemma source_full_unary_bound : bounded 2 source_full_unary_formula.
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

Definition source_full_binary M r p q := source_prop_binary M r p q \/
  (source_row_wf M r /\ source_case_ExE M r p q).
Definition source_full_binary_formula : form := source_prop_binary_formula ∨
  (source_row_wf_formula $0 ∧ source_case_ExE_formula).
Lemma source_full_binary_correct M rho r p q :
  holds M (r .: p .: q .: rho) source_full_binary_formula <-> source_full_binary M r p q.
Proof.
  unfold source_full_binary_formula,source_full_binary.
  rewrite holds_or, source_prop_binary_correct, holds_and. repeat setoid_rewrite holds_or.
  rewrite source_row_wf_formula_correct.
  rewrite source_case_ExE_correct.
  reflexivity.
Qed.
Lemma source_full_binary_bound : bounded 3 source_full_binary_formula.
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

Definition source_full_rules : NumericalRules :=
  {| rule_base_formula := source_prop_base_formula; rule_base_bound := source_prop_base_bound;
     rule_unary_formula := source_full_unary_formula; rule_unary_bound := source_full_unary_bound;
     rule_binary_formula := source_full_binary_formula; rule_binary_bound := source_full_binary_bound |}.
Lemma source_full_trace_base M r : trace_base M source_full_rules r <-> source_prop_base M r.
Proof. apply source_prop_base_correct. Qed.
Lemma source_full_trace_unary M r p : trace_unary M source_full_rules r p <-> source_full_unary M r p.
Proof. apply source_full_unary_correct. Qed.
Lemma source_full_trace_binary M r p q : trace_binary M source_full_rules r p q <-> source_full_binary M r p q.
Proof. apply source_full_binary_correct. Qed.
