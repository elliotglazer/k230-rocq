(** Inverting the literal quantifier block recovers the bound on its matrix. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs SetFormulaCodes
  SourceBounded SourceBallSRules SourceBallS SourceInternalLiftLaws.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
Definition balls_inverse_bound_at M n:=forall y body out k,
  source_ballS M n y body out ->source_bounded M out k ->source_bounded M body(addM M n k).
Local Opaque holds source_ballS_formula source_bounded_accept_formula.
Lemma balls_inverse_bound_definable M:Definable1 M(balls_inverse_bound_at M).
Proof.
  exists(∀∀∀∀(source_ballS_formula $4 $3 $2 $1 →source_bounded_accept_formula $1 $0 →
    source_bounded_accept_formula $2($4⊕$0))),(fun _=>zeroM M). intro n. unfold balls_inverse_bound_at.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite source_ballS_formula_correct. setoid_rewrite source_bounded_accept_formula_correct. reflexivity.
Qed.
Theorem source_ballS_inverse_bound M n:balls_inverse_bound_at M n.
Proof.
  revert n. apply(definable_induction M _ (balls_inverse_bound_definable M)).
  - intros y body out k HO HB. apply source_ballS_zero in HO. subst out. now rewrite coding_add_zero.
  - intros n IH y body out k HO HB. apply source_ballS_succ in HO.
    destruct HO as(previous&HP&atom&point&HA&HI&HQ).
    apply(proj1(source_bounded_accept_unary M SFAll point out k(or_introl eq_refl)HQ))in HB.
    apply(proj1(source_bounded_accept_binary M SFImpl atom previous point(succM M k)
      (or_intror(or_intror eq_refl))HI))in HB. destruct HB as[_ HB].
    pose proof(IH(succM M y)body previous(succM M k)HP HB)as H.
    rewrite internal_add_succ_right,<-Arithmetic.add_succ in H. exact H.
Qed.
Print Assumptions source_ballS_inverse_bound.
