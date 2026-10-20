(** Free-variable bounds of arbitrary internally many carrier-bounded
    quantifiers, proved by ordinary PA-definable count induction. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT FiniteCRTFormula
  CodeExpressions NumericalProofs SetFormulaCodes SourceBounded SourceBallSRules SourceBallS.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
Definition balls_bound_at M n:=forall y body out k,
  source_ballS M n y body out ->coding_lt M y k ->
  source_bounded M body(addM M n k) ->source_bounded M out k.
Local Opaque holds source_ballS_formula source_bounded_accept_formula Peano.sless.
Lemma balls_bound_definable M:Definable1 M(balls_bound_at M).
Proof.
  exists(∀∀∀∀(source_ballS_formula $4 $3 $2 $1 →Peano.sless $3 $0 →
    source_bounded_accept_formula $2($4 ⊕ $0) →source_bounded_accept_formula $1 $0)),
    (fun _=>zeroM M). intro n. unfold balls_bound_at.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite source_ballS_formula_correct. setoid_rewrite less_formula_correct.
  setoid_rewrite source_bounded_accept_formula_correct. reflexivity.
Qed.
Theorem source_ballS_bounded M n:balls_bound_at M n.
Proof.
  revert n. apply(definable_induction M _ (balls_bound_definable M)).
  - intros y body out k HO HY HB. apply source_ballS_zero in HO. subst out.
    now rewrite coding_add_zero in HB.
  - intros n IH y body out k HO HY HB. apply source_ballS_succ in HO.
    destruct HO as(previous&HP&atom&point&HA&HI&HQ).
    assert(HB':source_bounded M body(addM M n(succM M k))).
    { rewrite(coding_add_comm M n(succM M k)),Arithmetic.add_succ,(coding_add_comm M k n),<-Arithmetic.add_succ. exact HB. }
    pose proof(IH(succM M y)body previous(succM M k)HP
      (proj2(coding_lt_succ_cancel M y k)HY)HB')as BP.
    apply(proj2(source_bounded_accept_unary M SFAll point out k(or_introl eq_refl)HQ)).
    apply(proj2(source_bounded_accept_binary M SFImpl atom previous point(succM M k)
      (or_intror(or_intror eq_refl))HI)). split;[|exact BP].
    apply(proj2(source_bounded_accept_atom M SFMember(zeroM M)(succM M y)atom(succM M k)(or_introl eq_refl)HA)).
    split;[apply coding_zero_lt_succ|exact(proj2(coding_lt_succ_cancel M y k)HY)].
Qed.
Print Assumptions source_ballS_bounded.



