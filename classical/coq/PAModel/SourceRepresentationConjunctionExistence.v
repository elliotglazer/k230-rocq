(** Actual conjunction case of representation existence, in the canonical
    closure recipe. Its two proof premises are precisely the two child
    existence induction hypotheses, for arbitrary internal source codes. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceNumeralLift
 SourcePropositionalTemplates SourcePropRenaming SourceDescriptorProvability SourceDescriptorClosure SourceDescriptorPrograms
 SourceRepresentationRecipe SourceRepresentationClosureRecipe SourceRepresentationFalsityClosure
 SourceRepresentationNamedConstructor SourceRepresentationNamedConjunction SourceRepresentationConjunctionShell
 SourceRepresentationClosureNormalization SourceRepresentationConjunctionCoordinates SourceRepresentationNamedWitness
 SourceRepresentativeQuantifier SourceRepresentativeRenaming SourceNamedQuantifierRules
 SourceNamedDifferenceCertificates
 SourceParameterIdentityCalibration SourceFiniteNameParameters SourceDefinabilityPrimitives SourceZFRProvability SourceSetTheoryDescriptors
 NumericalRenamingMaps NumericalRenaming NumericalSourceFull FixedSourceBounds.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.

Definition RCE_environment M succ closure left right target i:=match i with
 |0=>succ|1=>closure|13=>target|14=>left|15=>right|_=>zeroM M end.
Definition RCE_left :=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 14)).
Definition RCE_right :=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 15)).
Definition RCE_result :=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 13)).
Ltac rce_ctx:=apply SPTCtx;cbn;auto 12.
Lemma RCE_program :source_prop_program [RCS_result;RCE_left;RCE_right]RCE_result.
Proof.
 unfold RCS_result,RCE_left,RCE_right,RCE_result. do 2 apply SPTII.
 eapply SPTIE with(a:=SPTSlot 15).
 - eapply SPTIE with(a:=SPTSlot 14).
   + eapply SPTIE with(a:=SPTSlot 1).
     * eapply SPTIE with(a:=SPTSlot 0);rce_ctx.
     * rce_ctx.
   + eapply SPTIE with(a:=SPTSlot 1).
     * eapply SPTIE with(a:=SPTSlot 0);rce_ctx.
     * rce_ctx.
 - eapply SPTIE with(a:=SPTSlot 1).
   + eapply SPTIE with(a:=SPTSlot 0);rce_ctx.
   + rce_ctx.
Qed.

Lemma source_auxiliary_representation_exists_rename M rep named r member matrix namedex targetbody targetex b c n delta :
 source_bounded M rep(code_numeral M 2) ->~coding_lt M r(code_numeral M 3) ->
 source_representative_renaming M r rep named ->sf_relation M SFMember r(code_numeral M 2)member ->
 sf_relation M SFAnd member named matrix ->source_named_quantifier M false r matrix namedex ->
 renaming_lookup M b c n delta(code_numeral M 1)(zeroM M) ->
 renaming_lookup M b c n delta(code_numeral M 2)(code_numeral M 2) ->
 sf_relation M SFAnd(representation_member_code M)rep targetbody ->sf_relation M SFEx targetbody(zeroM M)targetex ->
 numerical_renaming M namedex b c n delta targetex.
Proof.
 intros BRep HR HNamed HMember HMatrix HEx HOne HTwo HBody HTarget.
 destruct(sf_relation_total M SFAnd(representation_named_member02 M)rep)as(original&HO).
 destruct(source_named_quantifier_total M false(zeroM M)original)as(originalex&HOriginalEx).
 rewrite(source_representative_quantifier_normalization M false original matrix r(code_numeral M 3)namedex originalex
  (source_representation_witness_body_bound M rep original BRep HO) HR
  (source_representative_witness_body_renaming M r rep named member original matrix HNamed HMember HO HMatrix)HEx HOriginalEx).
 exact(source_named_representation_exists_rename M rep original originalex targetbody targetex b c n delta
  BRep HO HOriginalEx HOne HTwo HBody HTarget).
Qed.

Theorem source_zfr_representation_conjunction M count left right conjunction out :
 source_bounded M conjunction count ->sf_relation M SFAnd left right conjunction ->
 (forall child,source_representation_in_closure_recipe M count left child ->source_zfr_provable M child) ->
 (forall child,source_representation_in_closure_recipe M count right child ->source_zfr_provable M child) ->
 source_representation_in_closure_recipe M count conjunction out ->source_zfr_provable M out.
Proof.
 intros HBound HAnd IHLeft IHRight(rep&succ&closure&targetbody&targetex&middle&HR&HS&HC&HTB&HTE&HM&HO).
 destruct(proj1(source_bounded_accept_binary M SFAnd left right conjunction count(or_introl eq_refl)HAnd)HBound)as[BL BR].
 destruct(source_zfr_named_conjunction_recipe M count left right conjunction rep HBound HAnd HR)
  as(repL&repR&namedL&namedR&ml&mr&mt&el&er&et&namedlaw&HRL&HRR&HNL&HNR&HML&HMR&HMT&HEL&HER&HET&HNamedLaw&PNamedLaw).
 destruct(source_representation_in_closure_recipe_total M count left)as(outL&HLeft).
 pose proof(IHLeft outL HLeft)as PLeft.
 destruct HLeft as(repL'&succL&clL&bodyL&exL&middleL&HRL'&HSL&HCL&HBL&HEL'&HML'&HOL).
 assert(repL'=repL)by(eapply source_representation_recipe_functional;eassumption). subst repL'.
 assert(succL=succ)by(eapply code_relation_functional;eassumption). subst succL.
 assert(clL=closure)by(eapply code_relation_functional;eassumption). subst clL.
 destruct(source_representation_in_closure_recipe_total M count right)as(outR&HRight).
 pose proof(IHRight outR HRight)as PRight.
 destruct HRight as(repR'&succR&clR&bodyR&exR&middleR&HRR'&HSR&HCR&HBR&HER'&HMR'&HOR).
 assert(repR'=repR)by(eapply source_representation_recipe_functional;eassumption). subst repR'.
 assert(succR=succ)by(eapply code_relation_functional;eassumption). subst succR.
 assert(clR=closure)by(eapply code_relation_functional;eassumption). subst clR.
 destruct(source_representation_conjunction_coordinates_total M)as(b&c&HOne&HTwo&HSeven&HNS&HNC).
 assert(ES:succ=code_numeral M(sf_encode source_def_successor01)).
 { exact(code_relation_functional M representation_successor_expression(representation_identity_environment M)succ _ HS
   (source_parameter_identity_calibration M source_def_successor01(source_finite_parameter_names 3)
    (representation_identity_environment M)(representation_identity_names_graph M))). }
 assert(EC:closure=code_numeral M(sf_encode representation_closure_condition)).
 { exact(code_relation_functional M representation_closure_expression(representation_identity_environment M)closure _ HC
   (source_parameter_identity_calibration M representation_closure_condition(source_finite_parameter_names 3)
    (representation_identity_environment M)(representation_identity_names_graph M))). }
 assert(HSLift:numerical_renaming M(code_numeral M(sf_encode named_difference_successor))b c(code_numeral M 8)(zeroM M)succ).
 { rewrite ES. exact HNS. }
 assert(HCLift:numerical_renaming M(code_numeral M(sf_encode named_difference_closure))b c(code_numeral M 8)(zeroM M)closure).
 { rewrite EC. exact HNC. }
 assert(HELift:numerical_renaming M el b c(code_numeral M 8)(zeroM M)exL).
 { exact(source_auxiliary_representation_exists_rename M repL namedL(code_numeral M 3)(RNC_member M 3)ml el bodyL exL b c(code_numeral M 8)(zeroM M)
   (source_representation_recipe_bounded M count left repL BL HRL)
   ltac:(intro H;apply(proj1(fixed_source_numeral_lt_iff M 3 3))in H;lia)
   HNL(sf_make_numeral M SFMember 3 2)HML HEL HOne HTwo HBL HEL'). }
 assert(HERLift:numerical_renaming M er b c(code_numeral M 8)(zeroM M)exR).
 { exact(source_auxiliary_representation_exists_rename M repR namedR(code_numeral M 4)(RNC_member M 4)mr er bodyR exR b c(code_numeral M 8)(zeroM M)
   (source_representation_recipe_bounded M count right repR BR HRR)
   ltac:(intro H;apply(proj1(fixed_source_numeral_lt_iff M 4 3))in H;lia)
   HNR(sf_make_numeral M SFMember 4 2)HMR HER HOne HTwo HBR HER'). }
 assert(HETLift:numerical_renaming M et b c(code_numeral M 8)(zeroM M)targetex).
 { exact(source_named_representation_exists_rename M rep mt et targetbody targetex b c(code_numeral M 8)(zeroM M)
   (source_representation_recipe_bounded M count conjunction rep HBound HR)HMT HET HOne HTwo HTB HTE). }
 set(rho:=RCE_environment M succ closure exL exR targetex).
 destruct(code_relation_total M(source_prop_expression RCS_result)rho)as(law&HNormal).
 assert(HRename:numerical_renaming M namedlaw b c(code_numeral M 8)(zeroM M)law).
 { apply(source_prop_renaming M(RNC_environment M namedL namedR rep et el er)rho b c(code_numeral M 8)(zeroM M)
   RCS_result namedlaw law);[|exact HNamedLaw|exact HNormal].
   cbn[source_prop_slots RCS_result RNC_environment rho RCE_environment].
   exact(conj HSLift(conj HCLift(conj HELift(conj HERLift HETLift)))). }
 pose proof(source_descriptor_provable_renaming M ZFRSourceDescriptor namedlaw b c(code_numeral M 8)(zeroM M)law
  (proj2(source_zfr_descriptor_provable M namedlaw)PNamedLaw)HRename)as PLaw.
 pose proof PLaw as PTemp. destruct PTemp as(db&dc&dn&HDC&PFull).
 destruct(source_full_prv_wellformed M db dc dn law PFull)as(k&BLaw&BCtx).
 pose proof(source_prop_bound_inversion M rho RCS_result law k HNormal BLaw)as HBounds.
 cbn[source_prop_slots RCS_result rho RCE_environment]in HBounds.
 destruct HBounds as(BSucc&BCl&BExL&BExR&BTarget).
 assert(BAll:forall i,source_bounded M(rho i)k).
 { intros[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]];cbn[rho RCE_environment].
   - exact BSucc.
   - exact BCl.
   - apply source_bounded_accept_falsity.
   - apply source_bounded_accept_falsity.
   - apply source_bounded_accept_falsity.
   - apply source_bounded_accept_falsity.
   - apply source_bounded_accept_falsity.
   - apply source_bounded_accept_falsity.
   - apply source_bounded_accept_falsity.
   - apply source_bounded_accept_falsity.
   - apply source_bounded_accept_falsity.
   - apply source_bounded_accept_falsity.
   - apply source_bounded_accept_falsity.
   - exact BTarget.
   - exact BExL.
   - exact BExR.
   - apply source_bounded_accept_falsity. }
 assert(GLeft:code_relation M rho(source_prop_expression RCE_left)outL).
 { exact(source_prop_template_join M rho SFImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 14))succ middleL outL eq_refl
   (source_prop_template_join M rho SFImpl(SPTSlot 1)(SPTSlot 14)closure exL middleL eq_refl eq_refl HML')HOL). }
 assert(GRight:code_relation M rho(source_prop_expression RCE_right)outR).
 { exact(source_prop_template_join M rho SFImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 15))succ middleR outR eq_refl
   (source_prop_template_join M rho SFImpl(SPTSlot 1)(SPTSlot 15)closure exR middleR eq_refl eq_refl HMR')HOR). }
 assert(GOut:code_relation M rho(source_prop_expression RCE_result)out).
 { exact(source_prop_template_join M rho SFImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 13))succ middle out eq_refl
   (source_prop_template_join M rho SFImpl(SPTSlot 1)(SPTSlot 13)closure targetex middle eq_refl eq_refl HM)HO). }
 apply(proj1(source_zfr_descriptor_provable M out)).
 apply(source_descriptor_prop_program M ZFRSourceDescriptor _ _ RCE_program rho k out BAll);[|exact GOut].
 intros p[<-|[<-|[<-|[]]]]f HF.
 - rewrite(code_relation_functional M _ rho f law HF HNormal). exact PLaw.
 - rewrite(code_relation_functional M _ rho f outL HF GLeft). exact(proj2(source_zfr_descriptor_provable M outL)PLeft).
 - rewrite(code_relation_functional M _ rho f outR HF GRight). exact(proj2(source_zfr_descriptor_provable M outR)PRight).
Qed.

Print Assumptions source_zfr_representation_conjunction.
