(** Literal propositional FullND rules on numerical source sequents.
    The only auxiliary inference combines the two branches needed by DE.
    Every produced row is checked for syntactic well-formedness. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
  NumericalProofs NumericalContexts NumericalEnvironments SourceSequents SetFormulaCodes
  SourceBounded NumericalTraces SentenceBounds.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
Local Opaque holds source_sequent_formula source_branches_formula
  sf_formula environment_cons_formula context_member_formula source_row_wf_formula.

Definition source_case_Ctx M r := exists b c n f,
  ((source_sequent M b c n f r) /\ (context_member M b c n f)).
Definition source_case_Ctx_formula : form := ∃∃∃∃
  ((source_sequent_formula $3 $2 $1 $0 $4) ∧ (context_member_formula $3 $2 $1 $0)).
Lemma source_case_Ctx_correct M rho r :
  holds M (r .: rho) source_case_Ctx_formula <-> source_case_Ctx M r.
Proof.
  unfold source_case_Ctx_formula,source_case_Ctx.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite source_sequent_formula_correct.
  setoid_rewrite context_member_formula_correct.
  reflexivity.
Qed.

Definition source_case_Pc M r := exists b c n a d x y f,
  ((source_sequent M b c n f r) /\ ((sf_relation M SFImpl a d x) /\ ((sf_relation M SFImpl x a y) /\ (sf_relation M SFImpl y a f)))).
Definition source_case_Pc_formula : form := ∃∃∃∃∃∃∃∃
  ((source_sequent_formula $7 $6 $5 $0 $8) ∧ ((sf_formula SFImpl $4 $3 $2) ∧ ((sf_formula SFImpl $2 $4 $1) ∧ (sf_formula SFImpl $1 $4 $0)))).
Lemma source_case_Pc_correct M rho r :
  holds M (r .: rho) source_case_Pc_formula <-> source_case_Pc M r.
Proof.
  unfold source_case_Pc_formula,source_case_Pc.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite source_sequent_formula_correct.
  setoid_rewrite sf_formula_correct.
  reflexivity.
Qed.

Definition source_case_II M r p := exists b c n a d f u v l,
  ((source_sequent M b c n f r) /\ ((source_sequent M u v l d p) /\ ((environment_cons M b c n a u v l) /\ (sf_relation M SFImpl a d f)))).
Definition source_case_II_formula : form := ∃∃∃∃∃∃∃∃∃
  ((source_sequent_formula $8 $7 $6 $3 $9) ∧ ((source_sequent_formula $2 $1 $0 $4 $10) ∧ ((environment_cons_formula $8 $7 $6 $5 $2 $1 $0) ∧ (sf_formula SFImpl $5 $4 $3)))).
Lemma source_case_II_correct M rho r p :
  holds M (r .: p .: rho) source_case_II_formula <-> source_case_II M r p.
Proof.
  unfold source_case_II_formula,source_case_II.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite source_sequent_formula_correct.
  setoid_rewrite environment_cons_formula_correct.
  setoid_rewrite sf_formula_correct.
  reflexivity.
Qed.

Definition source_case_Exp M r p := exists b c n f,
  ((source_sequent M b c n f r) /\ (source_sequent M b c n (zeroM M) p)).
Definition source_case_Exp_formula : form := ∃∃∃∃
  ((source_sequent_formula $3 $2 $1 $0 $4) ∧ (source_sequent_formula $3 $2 $1 zero $5)).
Lemma source_case_Exp_correct M rho r p :
  holds M (r .: p .: rho) source_case_Exp_formula <-> source_case_Exp M r p.
Proof.
  unfold source_case_Exp_formula,source_case_Exp.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite source_sequent_formula_correct.
  reflexivity.
Qed.

Definition source_case_CE1 M r p := exists b c n a d f,
  ((source_sequent M b c n a r) /\ ((source_sequent M b c n f p) /\ (sf_relation M SFAnd a d f))).
Definition source_case_CE1_formula : form := ∃∃∃∃∃∃
  ((source_sequent_formula $5 $4 $3 $2 $6) ∧ ((source_sequent_formula $5 $4 $3 $0 $7) ∧ (sf_formula SFAnd $2 $1 $0))).
Lemma source_case_CE1_correct M rho r p :
  holds M (r .: p .: rho) source_case_CE1_formula <-> source_case_CE1 M r p.
Proof.
  unfold source_case_CE1_formula,source_case_CE1.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite source_sequent_formula_correct.
  setoid_rewrite sf_formula_correct.
  reflexivity.
Qed.

Definition source_case_CE2 M r p := exists b c n a d f,
  ((source_sequent M b c n d r) /\ ((source_sequent M b c n f p) /\ (sf_relation M SFAnd a d f))).
Definition source_case_CE2_formula : form := ∃∃∃∃∃∃
  ((source_sequent_formula $5 $4 $3 $1 $6) ∧ ((source_sequent_formula $5 $4 $3 $0 $7) ∧ (sf_formula SFAnd $2 $1 $0))).
Lemma source_case_CE2_correct M rho r p :
  holds M (r .: p .: rho) source_case_CE2_formula <-> source_case_CE2 M r p.
Proof.
  unfold source_case_CE2_formula,source_case_CE2.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite source_sequent_formula_correct.
  setoid_rewrite sf_formula_correct.
  reflexivity.
Qed.

Definition source_case_DI1 M r p := exists b c n a d f,
  ((source_sequent M b c n f r) /\ ((source_sequent M b c n a p) /\ (sf_relation M SFOr a d f))).
Definition source_case_DI1_formula : form := ∃∃∃∃∃∃
  ((source_sequent_formula $5 $4 $3 $0 $6) ∧ ((source_sequent_formula $5 $4 $3 $2 $7) ∧ (sf_formula SFOr $2 $1 $0))).
Lemma source_case_DI1_correct M rho r p :
  holds M (r .: p .: rho) source_case_DI1_formula <-> source_case_DI1 M r p.
Proof.
  unfold source_case_DI1_formula,source_case_DI1.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite source_sequent_formula_correct.
  setoid_rewrite sf_formula_correct.
  reflexivity.
Qed.

Definition source_case_DI2 M r p := exists b c n a d f,
  ((source_sequent M b c n f r) /\ ((source_sequent M b c n d p) /\ (sf_relation M SFOr a d f))).
Definition source_case_DI2_formula : form := ∃∃∃∃∃∃
  ((source_sequent_formula $5 $4 $3 $0 $6) ∧ ((source_sequent_formula $5 $4 $3 $1 $7) ∧ (sf_formula SFOr $2 $1 $0))).
Lemma source_case_DI2_correct M rho r p :
  holds M (r .: p .: rho) source_case_DI2_formula <-> source_case_DI2 M r p.
Proof.
  unfold source_case_DI2_formula,source_case_DI2.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite source_sequent_formula_correct.
  setoid_rewrite sf_formula_correct.
  reflexivity.
Qed.

Definition source_case_IE M r p q := exists b c n a d f,
  ((source_sequent M b c n d r) /\ ((source_sequent M b c n f p) /\ ((source_sequent M b c n a q) /\ (sf_relation M SFImpl a d f)))).
Definition source_case_IE_formula : form := ∃∃∃∃∃∃
  ((source_sequent_formula $5 $4 $3 $1 $6) ∧ ((source_sequent_formula $5 $4 $3 $0 $7) ∧ ((source_sequent_formula $5 $4 $3 $2 $8) ∧ (sf_formula SFImpl $2 $1 $0)))).
Lemma source_case_IE_correct M rho r p q :
  holds M (r .: p .: q .: rho) source_case_IE_formula <-> source_case_IE M r p q.
Proof.
  unfold source_case_IE_formula,source_case_IE.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite source_sequent_formula_correct.
  setoid_rewrite sf_formula_correct.
  reflexivity.
Qed.

Definition source_case_CI M r p q := exists b c n a d f,
  ((source_sequent M b c n f r) /\ ((source_sequent M b c n a p) /\ ((source_sequent M b c n d q) /\ (sf_relation M SFAnd a d f)))).
Definition source_case_CI_formula : form := ∃∃∃∃∃∃
  ((source_sequent_formula $5 $4 $3 $0 $6) ∧ ((source_sequent_formula $5 $4 $3 $2 $7) ∧ ((source_sequent_formula $5 $4 $3 $1 $8) ∧ (sf_formula SFAnd $2 $1 $0)))).
Lemma source_case_CI_correct M rho r p q :
  holds M (r .: p .: q .: rho) source_case_CI_formula <-> source_case_CI M r p q.
Proof.
  unfold source_case_CI_formula,source_case_CI.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite source_sequent_formula_correct.
  setoid_rewrite sf_formula_correct.
  reflexivity.
Qed.

Definition source_case_BranchPair M r p q := exists b c n a d f u v l x y z,
  ((source_branches M b c n a d f r) /\ ((source_sequent M u v l f p) /\ ((source_sequent M x y z f q) /\ ((environment_cons M b c n a u v l) /\ (environment_cons M b c n d x y z))))).
Definition source_case_BranchPair_formula : form := ∃∃∃∃∃∃∃∃∃∃∃∃
  ((source_branches_formula $11 $10 $9 $8 $7 $6 $12) ∧ ((source_sequent_formula $5 $4 $3 $6 $13) ∧ ((source_sequent_formula $2 $1 $0 $6 $14) ∧ ((environment_cons_formula $11 $10 $9 $8 $5 $4 $3) ∧ (environment_cons_formula $11 $10 $9 $7 $2 $1 $0))))).
Lemma source_case_BranchPair_correct M rho r p q :
  holds M (r .: p .: q .: rho) source_case_BranchPair_formula <-> source_case_BranchPair M r p q.
Proof.
  unfold source_case_BranchPair_formula,source_case_BranchPair.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite source_branches_formula_correct.
  setoid_rewrite source_sequent_formula_correct.
  setoid_rewrite environment_cons_formula_correct.
  reflexivity.
Qed.

Definition source_case_DE M r p q := exists b c n a d f disj,
  ((source_sequent M b c n f r) /\ ((source_sequent M b c n disj p) /\ ((source_branches M b c n a d f q) /\ (sf_relation M SFOr a d disj)))).
Definition source_case_DE_formula : form := ∃∃∃∃∃∃∃
  ((source_sequent_formula $6 $5 $4 $1 $7) ∧ ((source_sequent_formula $6 $5 $4 $0 $8) ∧ ((source_branches_formula $6 $5 $4 $3 $2 $1 $9) ∧ (sf_formula SFOr $3 $2 $0)))).
Lemma source_case_DE_correct M rho r p q :
  holds M (r .: p .: q .: rho) source_case_DE_formula <-> source_case_DE M r p q.
Proof.
  unfold source_case_DE_formula,source_case_DE.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite source_sequent_formula_correct.
  setoid_rewrite source_branches_formula_correct.
  setoid_rewrite sf_formula_correct.
  reflexivity.
Qed.

Definition source_prop_base M r := source_row_wf M r /\
  (source_case_Ctx M r \/ source_case_Pc M r).
Definition source_prop_base_formula : form := source_row_wf_formula $0 ∧
  (source_case_Ctx_formula ∨ source_case_Pc_formula).
Lemma source_prop_base_correct M rho r :
  holds M (r .: rho) source_prop_base_formula <-> source_prop_base M r.
Proof.
  unfold source_prop_base_formula,source_prop_base.
  rewrite holds_and. repeat setoid_rewrite holds_or.
  rewrite source_row_wf_formula_correct.
  rewrite source_case_Ctx_correct.
  rewrite source_case_Pc_correct.
  reflexivity.
Qed.
Lemma source_prop_base_bound : bounded 1 source_prop_base_formula.
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

Definition source_prop_unary M r p := source_row_wf M r /\
  (source_case_II M r p \/ (source_case_Exp M r p \/ (source_case_CE1 M r p \/ (source_case_CE2 M r p \/ (source_case_DI1 M r p \/ source_case_DI2 M r p))))).
Definition source_prop_unary_formula : form := source_row_wf_formula $0 ∧
  (source_case_II_formula ∨ (source_case_Exp_formula ∨ (source_case_CE1_formula ∨ (source_case_CE2_formula ∨ (source_case_DI1_formula ∨ source_case_DI2_formula))))).
Lemma source_prop_unary_correct M rho r p :
  holds M (r .: p .: rho) source_prop_unary_formula <-> source_prop_unary M r p.
Proof.
  unfold source_prop_unary_formula,source_prop_unary.
  rewrite holds_and. repeat setoid_rewrite holds_or.
  rewrite source_row_wf_formula_correct.
  rewrite source_case_II_correct.
  rewrite source_case_Exp_correct.
  rewrite source_case_CE1_correct.
  rewrite source_case_CE2_correct.
  rewrite source_case_DI1_correct.
  rewrite source_case_DI2_correct.
  reflexivity.
Qed.
Lemma source_prop_unary_bound : bounded 2 source_prop_unary_formula.
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

Definition source_prop_binary M r p q := source_row_wf M r /\
  (source_case_IE M r p q \/ (source_case_CI M r p q \/ (source_case_BranchPair M r p q \/ source_case_DE M r p q))).
Definition source_prop_binary_formula : form := source_row_wf_formula $0 ∧
  (source_case_IE_formula ∨ (source_case_CI_formula ∨ (source_case_BranchPair_formula ∨ source_case_DE_formula))).
Lemma source_prop_binary_correct M rho r p q :
  holds M (r .: p .: q .: rho) source_prop_binary_formula <-> source_prop_binary M r p q.
Proof.
  unfold source_prop_binary_formula,source_prop_binary.
  rewrite holds_and. repeat setoid_rewrite holds_or.
  rewrite source_row_wf_formula_correct.
  rewrite source_case_IE_correct.
  rewrite source_case_CI_correct.
  rewrite source_case_BranchPair_correct.
  rewrite source_case_DE_correct.
  reflexivity.
Qed.
Lemma source_prop_binary_bound : bounded 3 source_prop_binary_formula.
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

Definition source_propositional_rules : NumericalRules :=
  {| rule_base_formula := source_prop_base_formula; rule_base_bound := source_prop_base_bound;
     rule_unary_formula := source_prop_unary_formula; rule_unary_bound := source_prop_unary_bound;
     rule_binary_formula := source_prop_binary_formula; rule_binary_bound := source_prop_binary_bound |}.
Lemma source_prop_trace_base M r : trace_base M source_propositional_rules r <-> source_prop_base M r.
Proof. apply source_prop_base_correct. Qed.
Lemma source_prop_trace_unary M r p : trace_unary M source_propositional_rules r p <-> source_prop_unary M r p.
Proof. apply source_prop_unary_correct. Qed.
Lemma source_prop_trace_binary M r p q : trace_binary M source_propositional_rules r p q <-> source_prop_binary M r p q.
Proof. apply source_prop_binary_correct. Qed.
