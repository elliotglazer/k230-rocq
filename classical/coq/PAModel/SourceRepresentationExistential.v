(** Complete actual existential representation existence. The only
    source-proof premise is the genuine child existence induction hypothesis. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone SourceNumeralLift FixedSourceBounds
 SourceProjectionWitnessRoles SourceProjectionNamedWitness SourceProjectionWitnessShell SourceRepresentationRecipe SourceRepresentationClosureRecipe
 SourceEnvironmentCarrierRecipe SourceEnvironmentCarrierInduction SourceEnvironmentCarrierClosure SourceRepresentativeRenaming
 SourceRepresentationClosureTransport SourceNamedClosureExistence SourceRepresentationNamedConjunction SourceRepresentationNamedWitness SourceNamedQuantifierRules
 SourcePropositionalTemplates SourceDescriptorProvability SourceDescriptorPrograms SourceSetTheoryDescriptors SourceZFRProvability SourceNamedDifferenceCertificates SourceNamedDifferenceFacts.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.
Definition PEX_left:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 10)).
Definition PEX_right:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 11)).
Definition PEX_goal:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 12)).
Definition PEX_values M exAn exChild exTarget i:=match i with
 |0=>code_numeral M(sf_encode named_difference_successor)|1=>code_numeral M(sf_encode named_difference_closure)
 |10=>exAn|11=>exChild|12=>exTarget|_=>zeroM M end.
Lemma PEX_program:source_prop_program[PW_result;PEX_left;PEX_right]PEX_goal.
Proof.
 unfold PW_result,PEX_left,PEX_right,PEX_goal. do 2 apply SPTII.
 eapply SPTIE with(a:=SPTSlot 11).
 - eapply SPTIE with(a:=SPTSlot 10).
   + eapply SPTIE with(a:=SPTSlot 1);[|pw_ctx]. eapply SPTIE with(a:=SPTSlot 0);pw_ctx.
   + eapply SPTIE with(a:=SPTSlot 1);[|pw_ctx]. eapply SPTIE with(a:=SPTSlot 0);pw_ctx.
 - eapply SPTIE with(a:=SPTSlot 1);[|pw_ctx]. eapply SPTIE with(a:=SPTSlot 0);pw_ctx.
Qed.
Theorem source_zfr_representation_existential M count f existential out:
 source_bounded M existential count->sf_relation M SFEx f(zeroM M)existential->
 (forall child,source_representation_in_closure_recipe M(succM M count)f child->source_zfr_provable M child)->
 source_representation_in_closure_recipe M count existential out->source_zfr_provable M out.
Proof.
 intros BEx HEx IH HOut.
 pose proof(proj1(source_bounded_accept_unary M SFEx f existential count(or_intror eq_refl)HEx)BEx)as BF.
 destruct(source_representation_recipe_total M count existential)as(rep&HRep).
 destruct(source_representation_recipe_total M(succM M count)f)as(childrep&HChildRep).
 destruct(source_representation_in_closure_recipe_total M(succM M count)f)as(childout&HChildOut).
 pose proof(IH childout HChildOut)as PChildOut.
 pose proof(source_representation_closure_graph M(succM M count)f childrep childout HChildRep HChildOut)as HChildClosure.
 destruct(source_zfr_environment_carrier_total M count)as(carrier&carrierout&HCarrier&HCarrierClosure&PCarrierOut).
 destruct(source_representative_renaming_total M(code_numeral M 3)childrep)as(namedChild&HNamedChild).
 destruct(source_representative_renaming_total M(code_numeral M 4)carrier)as(namedAn&HNamedAn).
 pose proof(source_representation_recipe_bounded M count existential rep BEx HRep)as BRep.
 pose proof(source_representation_recipe_bounded M(succM M count)f childrep BF HChildRep)as BChildRep.
 pose proof(source_environment_carrier_recipe_bounded M count carrier HCarrier)as BCarrier.
 destruct(source_zfr_projection_witness_roles M count f existential rep childrep namedChild carrier namedAn BEx HEx HRep HChildRep HNamedChild HCarrier HNamedAn)
  as(op&inner&body&law&HOp&HInner&HBody&HLaw&PLaw).
 destruct(source_zfr_projection_named_witness M carrier childrep namedAn namedChild rep op inner body law
  BCarrier BChildRep BRep HNamedAn HNamedChild HOp HInner HBody HLaw PLaw)
  as(mAn&mChild&mTarget&exAn&exChild&exTarget&namedlaw&HAn&HChild&HTarget&HExAn&HExChild&HExTarget&HNamedLaw&PNamedLaw).
 destruct(code_relation_total M(source_prop_expression NCE_template)(named_closure_values M exAn))as(anlaw&GAnLaw).
 pose proof(source_zfr_named_closure_existence M carrier carrierout(code_numeral M 4)namedAn(RNC_member M 4)mAn exAn anlaw
  BCarrier HCarrierClosure PCarrierOut ltac:(intro H;apply(proj1(fixed_source_numeral_lt_iff M 4 3))in H;lia)
  HNamedAn(sf_make_numeral M SFMember 4 2)HAn HExAn GAnLaw)as PAnLaw.
 destruct(code_relation_total M(source_prop_expression NCE_template)(named_closure_values M exChild))as(childlaw&GChildLaw).
 pose proof(source_zfr_named_closure_existence M childrep childout(code_numeral M 3)namedChild(RNC_member M 3)mChild exChild childlaw
  BChildRep HChildClosure PChildOut ltac:(intro H;apply(proj1(fixed_source_numeral_lt_iff M 3 3))in H;lia)
  HNamedChild(sf_make_numeral M SFMember 3 2)HChild HExChild GChildLaw)as PChildLaw.
 set(rho:=PEX_values M exAn exChild exTarget).
 change(code_relation M rho(source_prop_expression PW_result)namedlaw)in HNamedLaw.
 change(code_relation M rho(source_prop_expression PEX_left)anlaw)in GAnLaw.
 change(code_relation M rho(source_prop_expression PEX_right)childlaw)in GChildLaw.
 pose proof(source_representation_witness_body_bound M rep mTarget BRep HTarget)as BMTarget.
 pose proof(source_named_quantifier_bound M false(zeroM M)mTarget exTarget(code_numeral M 3)BMTarget HExTarget)as BExTarget.
 destruct(sf_relation_total M SFAnd(representation_named_member02 M)carrier)as(originalAn&HOAn).
 destruct(sf_relation_total M SFAnd(representation_named_member02 M)childrep)as(originalChild&HOChild).
 pose proof(source_representation_named_witness_bound M(code_numeral M 4)carrier namedAn(RNC_member M 4)originalAn mAn exAn BCarrier
  ltac:(intro H;apply(proj1(fixed_source_numeral_lt_iff M 4 3))in H;lia)HNamedAn(sf_make_numeral M SFMember 4 2)HOAn HAn HExAn)as BExAn.
 pose proof(source_representation_named_witness_bound M(code_numeral M 3)childrep namedChild(RNC_member M 3)originalChild mChild exChild BChildRep
  ltac:(intro H;apply(proj1(fixed_source_numeral_lt_iff M 3 3))in H;lia)HNamedChild(sf_make_numeral M SFMember 3 2)HOChild HChild HExChild)as BExChild.
 assert(BAll:forall i,source_bounded M(rho i)(code_numeral M 8)).
 { intros[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]];cbn[rho PEX_values].
   - exact(proj1(named_difference_fixed_bounds M)).
   - exact(proj2(named_difference_fixed_bounds M)).
   - apply source_bounded_accept_falsity.
   - apply source_bounded_accept_falsity.
   - apply source_bounded_accept_falsity.
   - apply source_bounded_accept_falsity.
   - apply source_bounded_accept_falsity.
   - apply source_bounded_accept_falsity.
   - apply source_bounded_accept_falsity.
   - apply source_bounded_accept_falsity.
   - exact(source_bounded_monotone M exAn _ _ BExAn(proj2(fixed_source_numeral_lt_iff M 3 9)ltac:(lia))).
   - exact(source_bounded_monotone M exChild _ _ BExChild(proj2(fixed_source_numeral_lt_iff M 3 9)ltac:(lia))).
   - exact(source_bounded_monotone M exTarget _ _ BExTarget(proj2(fixed_source_numeral_lt_iff M 3 9)ltac:(lia))).
   - apply source_bounded_accept_falsity. }
 destruct(code_relation_total M(source_prop_expression NCE_template)(named_closure_values M exTarget))as(result&GResult).
 assert(GResult':code_relation M rho(source_prop_expression PEX_goal)result)by(exact GResult).
 assert(PResult:source_zfr_provable M result).
 { apply(proj1(source_zfr_descriptor_provable M result)).
   apply(source_descriptor_prop_program M ZFRSourceDescriptor _ _ PEX_program rho(code_numeral M 8)result BAll);[|exact GResult'].
   intros p[<-|[<-|[<-|[]]]]value HG.
   - rewrite(code_relation_functional M _ rho value namedlaw HG HNamedLaw). exact(proj2(source_zfr_descriptor_provable M namedlaw)PNamedLaw).
   - rewrite(code_relation_functional M _ rho value anlaw HG GAnLaw). exact(proj2(source_zfr_descriptor_provable M anlaw)PAnLaw).
   - rewrite(code_relation_functional M _ rho value childlaw HG GChildLaw). exact(proj2(source_zfr_descriptor_provable M childlaw)PChildLaw). }
 exact(source_zfr_named_representation_closure M rep mTarget exTarget result out BRep
  (source_representation_closure_graph M count existential rep out HRep HOut)HTarget HExTarget GResult PResult).
Qed.
Print Assumptions source_zfr_representation_existential.
