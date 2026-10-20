(** Complete actual An successor existence proof in the canonical closure
    statement. Its only proof premise is the preceding-count induction
    hypothesis, with no pointwise operation or quantifier premise. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceNumeralLift SourcePropositionalTemplates
 SourcePropRenaming SourceDescriptorProvability SourceDescriptorClosure SourceDescriptorPrograms SourceZFRProvability SourceSetTheoryDescriptors
 SourceEnvironmentCarrierRecipe SourceEnvironmentCarrierClosure SourceEnvironmentCarrierNamedStep SourceEnvironmentNamedWitness
 SourceEnvironmentWitnessShell SourceRepresentationFalsityClosure SourceRepresentationClosureRecipe SourceRepresentationConjunctionCoordinates
 SourceRepresentationConjunctionExistence SourceRepresentationClosureNormalization SourceRepresentationNamedConjunction
 SourceRepresentativeRenaming SourceNamedQuantifierRules SourceDefinabilityPrimitives SourceNamedDifferenceCertificates
 NumericalRenamingMaps NumericalRenaming NumericalSourceFull SourceSequents FixedSourceBounds.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.
Definition EC_step_values M succ closure previous target i:=match i with
 |0=>succ|1=>closure|9=>previous|10=>target|_=>zeroM M end.
Definition EC_step_previous:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 9)).
Definition EC_step_target:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 10)).
Lemma EC_step_program:source_prop_program[ECW_result;EC_step_previous]EC_step_target.
Proof.
 unfold ECW_result,EC_step_previous,EC_step_target. do 2 apply SPTII.
 eapply SPTIE with(a:=SPTSlot 9).
 - eapply SPTIE with(a:=SPTSlot 1);[|apply SPTCtx;cbn;auto 10].
   eapply SPTIE with(a:=SPTSlot 0);apply SPTCtx;cbn;auto 10.
 - eapply SPTIE with(a:=SPTSlot 1);[|apply SPTCtx;cbn;auto 10].
   eapply SPTIE with(a:=SPTSlot 0);apply SPTCtx;cbn;auto 10.
Qed.
Theorem source_zfr_environment_carrier_step M count:
 source_environment_carrier_proof_at M count ->source_environment_carrier_proof_at M(succM M count).
Proof.
 intros IH result out HR HOut.
 destruct(source_environment_carrier_recipe_total M count)as(previous&HP).
 pose proof(source_environment_carrier_recipe_bounded M count previous HP)as BP.
 pose proof(source_environment_carrier_recipe_bounded M(succM M count)result HR)as BR.
 destruct(source_representative_renaming_total M(code_numeral M 3)previous)as(named&HNamed).
 destruct(source_zfr_environment_carrier_named_step M count previous result named HP HR HNamed)
 as(op&inner&point&HOp&HInner&HPoint&PPoint).
 destruct(source_zfr_environment_named_witness M previous named result op inner point BP BR HNamed HOp HInner HPoint PPoint)
 as(oldbody&targetbody&oldex&targetex&namedlaw&HOldBody&HTargetBody&HOldEx&HTargetEx&GNamedLaw&PNamedLaw).
 set(succ:=code_numeral M(sf_encode source_def_successor01)).
 set(closure:=code_numeral M(sf_encode representation_closure_condition)).
 destruct(sf_relation_total M SFAnd(representation_member_code M)previous)as(previousbody&HPreviousBody).
 destruct(sf_relation_total M SFEx previousbody(zeroM M))as(previousex&HPreviousEx).
 destruct(sf_relation_total M SFImpl closure previousex)as(previousmiddle&HPreviousMiddle).
 destruct(sf_relation_total M SFImpl succ previousmiddle)as(previousout&HPreviousOut).
 pose proof(source_environment_carrier_closure_statement_join M previous previousbody previousex previousmiddle previousout
  HPreviousBody HPreviousEx HPreviousMiddle HPreviousOut)as HPreviousClosure.
 pose proof(IH previous previousout HP HPreviousClosure)as PPrevious.
 destruct(sf_relation_total M SFAnd(representation_member_code M)result)as(resultbody&HResultBody).
 destruct(sf_relation_total M SFEx resultbody(zeroM M))as(resultex&HResultEx).
 destruct(sf_relation_total M SFImpl closure resultex)as(resultmiddle&HResultMiddle).
 destruct(sf_relation_total M SFImpl succ resultmiddle)as(resultout&HResultOut).
 pose proof(source_environment_carrier_closure_statement_join M result resultbody resultex resultmiddle resultout
  HResultBody HResultEx HResultMiddle HResultOut)as HResultClosure.
 assert(EOut:out=resultout)by(eapply source_environment_carrier_closure_statement_functional;eassumption). subst out.
 destruct(source_representation_conjunction_coordinates_total M)as(b&c&HOne&HTwo&HSeven&HNS&HNC).
 assert(ROld:numerical_renaming M oldex b c(code_numeral M 8)(zeroM M)previousex).
 { exact(source_auxiliary_representation_exists_rename M previous named(code_numeral M 3)(RNC_member M 3)oldbody oldex
   previousbody previousex b c(code_numeral M 8)(zeroM M)BP
   ltac:(intro H;apply(proj1(fixed_source_numeral_lt_iff M 3 3))in H;lia)
   HNamed(sf_make_numeral M SFMember 3 2)HOldBody HOldEx HOne HTwo HPreviousBody HPreviousEx). }
 assert(RTarget:numerical_renaming M targetex b c(code_numeral M 8)(zeroM M)resultex).
 { exact(source_named_representation_exists_rename M result targetbody targetex resultbody resultex b c(code_numeral M 8)(zeroM M)
   BR HTargetBody HTargetEx HOne HTwo HResultBody HResultEx). }
 set(values:=EC_step_values M succ closure previousex resultex).
 destruct(code_relation_total M(source_prop_expression ECW_result)values)as(law&GLaw).
 assert(RLaw:numerical_renaming M namedlaw b c(code_numeral M 8)(zeroM M)law).
 { apply(source_prop_renaming M(ECN_values M named result oldex targetex)values b c(code_numeral M 8)(zeroM M)
   ECW_result namedlaw law);[|exact GNamedLaw|exact GLaw].
   cbn[source_prop_slots ECW_result ECN_values values EC_step_values]. exact(conj HNS(conj HNC(conj ROld RTarget))). }
 pose proof(source_descriptor_provable_renaming M ZFRSourceDescriptor namedlaw b c(code_numeral M 8)(zeroM M)law
  (proj2(source_zfr_descriptor_provable M namedlaw)PNamedLaw)RLaw)as PLaw.
 pose proof PLaw as PTemp. destruct PTemp as(db&dc&dn&HCtx&PFull).
 destruct(source_full_prv_wellformed M db dc dn law PFull)as(k&BLaw&BCtx).
 pose proof(source_prop_bound_inversion M values ECW_result law k GLaw BLaw)as HBounds.
 cbn[source_prop_slots ECW_result values EC_step_values]in HBounds.
 destruct HBounds as(BSucc&BClosure&BPrevious&BResult).
 assert(BValues:forall i,source_bounded M(values i)k).
 { intros[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]];cbn[values EC_step_values].
   - exact BSucc.
   - exact BClosure.
   - apply source_bounded_accept_falsity.
   - apply source_bounded_accept_falsity.
   - apply source_bounded_accept_falsity.
   - apply source_bounded_accept_falsity.
   - apply source_bounded_accept_falsity.
   - apply source_bounded_accept_falsity.
   - apply source_bounded_accept_falsity.
   - exact BPrevious.
   - exact BResult.
   - apply source_bounded_accept_falsity. }
 assert(GPrevious:code_relation M values(source_prop_expression EC_step_previous)previousout).
 { eapply environment_carrier_code_join;[reflexivity| |exact HPreviousOut].
   eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HPreviousMiddle]. }
 assert(GResult:code_relation M values(source_prop_expression EC_step_target)resultout).
 { eapply environment_carrier_code_join;[reflexivity| |exact HResultOut].
   eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HResultMiddle]. }
 apply(proj1(source_zfr_descriptor_provable M resultout)).
 apply(source_descriptor_prop_program M ZFRSourceDescriptor _ _ EC_step_program values k resultout BValues);[|exact GResult].
 intros p[<-|[<-|[]]]f HF.
 - rewrite(code_relation_functional M _ values f law HF GLaw). exact PLaw.
 - rewrite(code_relation_functional M _ values f previousout HF GPrevious). exact(proj2(source_zfr_descriptor_provable M previousout)PPrevious).
Qed.
Print Assumptions source_zfr_environment_carrier_step.
