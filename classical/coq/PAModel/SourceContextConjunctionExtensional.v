(** Changing only the beta representation of a source context preserves
    its exact internally finite conjunction code. *)
From PAModel Require Import Model FiniteCoding FiniteCRT FiniteCRTFormula CodeExpressions NumericalProofs
  SetFormulaCodes SourceContextConjunction.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_context_same_rows M b c d e n :=forall i f g,
  coding_lt M i n ->beta M b c i f ->beta M d e i g ->f=g.
Definition source_context_same_rows_formula (b c d e n:term):form :=
  ∀∀∀ (Peano.sless $2 n`[↑]`[↑]`[↑] →
    beta_formula b`[↑]`[↑]`[↑] c`[↑]`[↑]`[↑] $2 $1 →
    beta_formula d`[↑]`[↑]`[↑] e`[↑]`[↑]`[↑] $2 $0 →$1==$0).
Local Opaque holds beta_formula.
Lemma source_context_same_rows_formula_correct M rho b c d e n :
  holds M rho (source_context_same_rows_formula b c d e n) <->
  source_context_same_rows M (evalM M rho b)(evalM M rho c)(evalM M rho d)(evalM M rho e)(evalM M rho n).
Proof.
  unfold source_context_same_rows_formula,source_context_same_rows.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite holds_sless. setoid_rewrite beta_formula_correct.
  setoid_rewrite source_context_conjunction_equality_correct.
  unfold evalM. repeat setoid_rewrite eval_up. reflexivity.
Qed.

Definition source_context_conjunction_extensional_at M b c d e n :=forall f g,
  source_context_conjunction M b c n f ->source_context_conjunction M d e n g ->
  source_context_same_rows M b c d e n ->f=g.
Definition source_context_conjunction_extensional_formula:form :=
  ∀∀(source_context_conjunction_formula $3 $4 $2 $1 →
    source_context_conjunction_formula $5 $6 $2 $0 →source_context_same_rows_formula $3 $4 $5 $6 $2 →$1==$0).
Local Opaque source_context_conjunction_formula source_context_same_rows_formula.
Lemma source_context_conjunction_extensional_definable M b c d e :
  Definable1 M (source_context_conjunction_extensional_at M b c d e).
Proof.
  exists source_context_conjunction_extensional_formula,(b .: c .: d .: e .: fun _=>zeroM M). intro n.
  unfold source_context_conjunction_extensional_at,source_context_conjunction_extensional_formula.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite source_context_conjunction_formula_correct.
  setoid_rewrite source_context_same_rows_formula_correct.
  setoid_rewrite source_context_conjunction_equality_correct. reflexivity.
Qed.

Theorem source_context_conjunction_extensional M b c d e :
  forall n,source_context_conjunction_extensional_at M b c d e n.
Proof.
  apply (definable_induction M (source_context_conjunction_extensional_at M b c d e)
    (source_context_conjunction_extensional_definable M b c d e)).
  - intros f g HF HG HSame. apply source_context_conjunction_zero in HF.
    apply source_context_conjunction_zero in HG. exact (sf_relation_functional M SFImpl (zeroM M)(zeroM M) f g HF HG).
  - intros n IH f g HF HG HSame.
    apply source_context_conjunction_succ in HF. apply source_context_conjunction_succ in HG.
    destruct HF as [p [h [HP [HH HF]]]];destruct HG as [q [j [HQ [HJ HG]]]].
    assert (E:p=q).
    { apply (IH p q HP HQ). intros i a z HI HA HZ.
      exact (HSame i a z (coding_lt_trans M i n (succM M n) HI (coding_lt_succ M n)) HA HZ). }
    subst q. pose proof (HSame n h j (coding_lt_succ M n) HH HJ) as E. subst j.
    exact (sf_relation_functional M SFAnd p h f g HF HG).
Qed.

Print Assumptions source_context_same_rows_formula_correct.
Print Assumptions source_context_conjunction_extensional_definable.
Print Assumptions source_context_conjunction_extensional.
