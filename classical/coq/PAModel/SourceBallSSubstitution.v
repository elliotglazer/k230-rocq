(** Arbitrary internally deep substitution commutes with literal ballS.
    All maps and source transformations are actual numerical graphs. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
  SetFormulaCodes NumericalSubstitutionMaps NumericalSubstitution
  SourceBallSRules SourceBallS SourceInternalLifts SourceInternalLiftLaws.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
Definition balls_substitution_at M count:=forall y body out b c n base y' body' out' ub uc,
  substitution_lookup M b c n base y y' ->source_ballS M count y body out ->
  source_upn_map M count b c n base ub uc ->
  numerical_substitution M body ub uc(addM M count n)(addM M count base)body' ->
  numerical_substitution M out b c n base out' ->source_ballS M count y' body' out'.
Definition balls_substitution_formula:form:=∀∀∀∀∀∀∀∀∀∀∀∀(
  substitution_lookup_formula $8 $7 $6 $5 $11 $4 →source_ballS_formula $12 $11 $10 $9 →
  source_upn_map_formula $12 $8 $7 $6 $5 $1 $0 →
  numerical_substitution_formula $10 $1 $0($12⊕$6)($12⊕$5)$3 →
  numerical_substitution_formula $9 $8 $7 $6 $5 $2 →source_ballS_formula $12 $4 $3 $2).
Local Opaque holds substitution_lookup_formula source_ballS_formula source_upn_map_formula numerical_substitution_formula.
Lemma balls_substitution_definable M:Definable1 M(balls_substitution_at M).
Proof.
  exists balls_substitution_formula,(fun _=>zeroM M). intro count.
  unfold balls_substitution_formula,balls_substitution_at.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite substitution_lookup_formula_correct. setoid_rewrite source_ballS_formula_correct.
  setoid_rewrite source_upn_map_formula_correct. setoid_rewrite numerical_substitution_formula_correct.
  reflexivity.
Qed.
Theorem source_ballS_substitution M count:balls_substitution_at M count.
Proof.
  revert count. apply(definable_induction M _ (balls_substitution_definable M)).
  - intros y body out b c n base y' body' out' ub uc HY HB HM HBody HOut.
    apply source_ballS_zero in HB. subst out. rewrite!coding_add_zero in HBody.
    pose proof(source_upn_map_zero M b c n base ub uc HM)as HE.
    pose proof(proj1(numerical_substitution_extensional M body ub uc n b c n base body' HE)HBody)as HBodyOld.
    pose proof(numerical_substitution_functional M body b c n base body' out' HBodyOld HOut)as E.
    apply source_ballS_zero. symmetry. exact E.
  - intros count IH y body out b c n base y' body' out' ub uc HY HB HM HBody HOut.
    apply source_ballS_succ in HB. destruct HB as(previous&HP&atom&point&HA&HI&HQ).
    destruct(proj1(numerical_substitution_quantifier M true point out b c n base out' HQ)HOut)
      as(lb&lc&ln&point'&HL&HPoint&HQ').
    destruct(proj1(numerical_substitution_binary M SFImpl atom previous point lb lc ln(succM M base)point'
      (or_intror(or_intror eq_refl))HI)HPoint)as(atom'&previous'&HAtom&HPrevious&HI').
    destruct(proj1(numerical_substitution_member M(zeroM M)(succM M y)atom lb lc ln(succM M base)atom' HA)HAtom)
      as(x&z&HX&HZ&HA').
    pose proof(proj1(substitution_lift_head M b c n base lb lc ln x HL)HX)as E. subst x.
    pose proof(proj2(substitution_lift_tail M b c n base lb lc ln y y' HL)HY)as HY'.
    pose proof(substitution_lookup_functional M lb lc ln(succM M base)(succM M y)z(succM M y')HZ HY')as E. subst z.
    destruct(source_upn_map_total M count lb lc ln(succM M base))as(vb&vc&HSmall).
    pose proof(source_upn_map_after_lift M count b c n base lb lc ln vb vc HL HSmall)as HFull.
    assert(HEquiv:substitution_equivalent M ub uc(addM M(succM M count)n)
      vb vc(addM M(succM M count)n)(addM M(succM M count)base)).
    { intros i v. rewrite(HM i v),(HFull i v). reflexivity. }
    pose proof(proj1(numerical_substitution_extensional M body ub uc(addM M(succM M count)n)
      vb vc(addM M(succM M count)n)(addM M(succM M count)base)body' HEquiv)HBody)as HBodyFull.
    assert(Elen:addM M count ln=addM M(succM M count)n).
    { destruct HL as[-> _]. rewrite internal_add_succ_right,Arithmetic.add_succ. reflexivity. }
    assert(Ebase:addM M count(succM M base)=addM M(succM M count)base).
    { rewrite internal_add_succ_right,Arithmetic.add_succ. reflexivity. }
    assert(HBodySmall:numerical_substitution M body vb vc(addM M count ln)(addM M count(succM M base))body').
    { now rewrite Elen,Ebase. }
    pose proof(IH(succM M y)body previous lb lc ln(succM M base)(succM M y')body' previous' vb vc
      HY' HP HSmall HBodySmall HPrevious)as HChild.
    apply source_ballS_succ. exists previous'. split;[exact HChild|]. exists atom',point'. auto.
Qed.
Print Assumptions source_ballS_substitution.
