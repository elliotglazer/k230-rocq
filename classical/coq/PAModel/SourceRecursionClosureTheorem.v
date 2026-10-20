(** The genuine uniform generic recursion theorem inside any PA model.
    Every Separation,Replacement,induction and carrier witness is constructed
    and discharged in the numerical source proof calculus. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded FixedSourceBounds NumericalContexts NumericalSourceFull
 SourceFiniteTelescope SourceFiniteTelescopeExists SourceZFRFiniteRule
 SourceRecursionStructureInputs SourceRecursionRangeBackground SourceRecursionRangeReplacement SourceRecursionRangeReplacementShell SourceRecursionRangeChart
 SourceRecursionClosureExists SourceRecursionCarrierExists SourceZFRProvability.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_rec_closure_theorem M phi A target law:
 source_bounded M phi(code_numeral M 2) ->source_rec_structure_inputs M phi(code_numeral M 0)(code_numeral M 2)A ->
 source_rec_closure_exists M phi(code_numeral M 1)target ->source_finite_telescope M A target law ->source_zfr_provable M law.
Proof.
 intros BP HA HTarget HLaw.
 assert(B0:coding_lt M(code_numeral M 0)(code_numeral M 3))by(apply(proj2(fixed_source_numeral_lt_iff M 0 3));lia).
 assert(B1:coding_lt M(code_numeral M 1)(code_numeral M 3))by(apply(proj2(fixed_source_numeral_lt_iff M 1 3));lia).
 assert(B2:coding_lt M(code_numeral M 2)(code_numeral M 3))by(apply(proj2(fixed_source_numeral_lt_iff M 2 3));lia).
 pose proof(source_rec_structure_inputs_bounded M phi(code_numeral M 0)(code_numeral M 2)A(code_numeral M 3)BP B0 B2 HA)as Bounds.
 pose proof(source_rec_closure_exists_bounded M phi(code_numeral M 1)target(code_numeral M 3)BP B1 HTarget)as BTarget.
 pose proof HA as HStructure.
 destruct HA as(funlaw&totalG&nonzero&injective&totality&induction&member&E&HFun&HG&HNZ&HInj&HT&HI&HM). subst A.
 set(background:=[funlaw;totality;induction;member]).
 assert(HBack:source_rec_rr_background M phi(code_numeral M 0)(code_numeral M 2)background).
 { exists funlaw,totality,induction,member. split;[reflexivity|]. auto. }
 destruct(source_zfr_rec_rr_range_total M phi background BP HBack)
  as(matrix&p2&range&rangeLaw&HMatrix&HP2&HRange&HRangeLaw&PRangeLaw).
 destruct(source_rec_rr_range_shell M phi p2 range HP2 HRange)as(body&HBody&HEx).
 assert(BRange:source_bounded M range(code_numeral M 3)).
 { apply(proj2(source_bounded_accept_unary M SFEx body range(code_numeral M 3)(or_intror eq_refl)HEx)).
   apply(source_rec_range_chart_bounded M phi(code_numeral M 1)(code_numeral M 2)(code_numeral M 3)(code_numeral M 0)body(code_numeral M 4)BP);
    try(apply(proj2(fixed_source_numeral_lt_iff M _ _));lia);exact HBody. }
 destruct(source_rec_structure_inputs_total M phi(code_numeral M 1)(code_numeral M 3))as(AS&HAS).
 pose proof(source_rec_structure_inputs_shift M phi(code_numeral M 0)(code_numeral M 2)
  [funlaw;totalG;nonzero;injective;totality;induction;member]AS BP HStructure HAS)as HS.
 destruct(source_rec_closure_exists_total M phi(code_numeral M 2))as(targetS&HTargetS).
 pose proof(source_rec_closure_exists_shift M phi(code_numeral M 1)target targetS BP HTarget HTargetS)as STarget.
 destruct(source_finite_telescope_total M(AS++[body])targetS)as(branch&HBranch).
 assert(PBranch:source_zfr_provable M branch).
 { apply(source_zfr_rec_carrier_exists M phi(code_numeral M 1)(code_numeral M 2)(code_numeral M 3)(code_numeral M 0)AS body targetS branch(code_numeral M 4)BP);
    try(apply(proj2(fixed_source_numeral_lt_iff M _ _));lia);assumption. }
 destruct(source_finite_telescope_total M([funlaw;totalG;nonzero;injective;totality;induction;member]++[range])target)as(exLaw&HExLaw).
 pose proof(source_zfr_finite_telescope_exists M[funlaw;totalG;nonzero;injective;totality;induction;member]AS body range target targetS branch exLaw(code_numeral M 3)
  Bounds BRange BTarget HS HEx STarget HBranch HExLaw PBranch)as PExLaw.
 apply(source_zfr_finite_rule M[rangeLaw;exLaw][funlaw;totalG;nonzero;injective;totality;induction;member]target law(code_numeral M 3)Bounds BTarget HLaw).
 - intros x[<-|[<-|[]]];assumption.
 - intros cb cc cn BC Laws Premises.
   assert(PRange:source_full_prv M cb cc cn range).
   { apply(source_full_finite_telescope_apply M background range rangeLaw HRangeLaw cb cc cn).
     - apply Laws. now left.
     - intros x HX. apply Premises. unfold background in HX. cbn in HX|-*. tauto. }
   apply(source_full_finite_telescope_apply M([funlaw;totalG;nonzero;injective;totality;induction;member]++[range])target exLaw HExLaw cb cc cn).
   + apply Laws. right. now left.
   + intros x HX. apply in_app_or in HX. destruct HX as[HX|[<-|[]]];[exact(Premises x HX)|exact PRange].
Qed.
Print Assumptions source_zfr_rec_closure_theorem.
