(** Actual member/equality representation point for arbitrary internal
    indices and assignment length. It uses the proved numerical lookup
    theorem twice and the pinned atomic operation theorem. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 SourceDefinabilityBounds SourceFiniteCutoffShift NumericalInstantiation SourceEnvFLookupProfile SourceAtomicReverseIndices
 SourceAtomicLookup SourceAtomicOperationSyntax SourceAtomicOperationShell SourceAtomicPointProgram
 SourceEnvFLookupFiniteProofs SourcePropositionalTemplates SourceWitnessProofComposition SourceZFRProvability SourceIffGraphs.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Local Ltac ap_graph:=lazymatch goal with
 | |-code_relation ?M ?rho(source_prop_expression(SPTSlot ?idx))?out=>reflexivity
 | |-code_relation ?M ?rho(source_prop_expression(SPTImpl ?A ?B))?out=>
  match goal with H:sf_relation M SFImpl ?a ?b out|-_=>apply(source_prop_template_join M rho SFImpl A B a b out);[ap_graph|ap_graph|exact H]end
 | |-code_relation ?M ?rho(source_prop_expression(SPTAnd ?A ?B))?out=>
  match goal with H:sf_relation M SFAnd ?a ?b out|-_=>apply(source_prop_template_join M rho SFAnd A B a b out);[ap_graph|ap_graph|exact H]end
 end.
Theorem source_zfr_atomic_representation_point M(member:bool)count i j ki kj environment first guard numI numJ xi xj namedI namedJ carrier representative op memCarrier atom memRepresentative equiv:
 source_reverse_index M count i ki->source_reverse_index M count j kj->source_envf M count environment->
 source_numf M ki numI->source_numf M kj numJ->source_cutoff_shift M 1 environment first->source_cutoff_shift M 1 first guard->
 numerical_instantiation M numI xi namedI->numerical_instantiation M numJ xj namedJ->
 source_atomic_operation M member carrier xi xj representative op->sf_relation M SFMember(zeroM M)carrier memCarrier->
 sf_relation M(if member then SFMember else SFEqual)(succM M(succM M(succM M i)))(succM M(succM M(succM M j)))atom->
 sf_relation M SFMember(zeroM M)representative memRepresentative->source_iff_graph M memRepresentative atom equiv->
 exists nums condition oldpoint newpoint pointmap result,
 sf_relation M SFAnd namedI namedJ nums/\sf_relation M SFAnd op nums condition/\
 sf_relation M SFImpl guard memCarrier oldpoint/\sf_relation M SFImpl guard equiv newpoint/\
 sf_relation M SFImpl oldpoint newpoint pointmap/\sf_relation M SFImpl condition pointmap result/\source_zfr_provable M result.
Proof.
 intros HI HJ HEnv HNumI HNumJ HFirst HGuard HNamedI HNamedJ HOp HCarrier HAtom HRepresentative HIff.
 destruct(source_env_profile_total M(zeroM M)xi(succM M(succM M(succM M i))))as(left&HLeft).
 destruct(source_env_profile_total M(zeroM M)xj(succM M(succM M(succM M j))))as(right&HRight).
 destruct(sf_relation_total M SFImpl namedI left)as(leftInner&HLeftInner).
 destruct(sf_relation_total M SFImpl guard leftInner)as(leftLaw&HLeftLaw).
 pose proof(source_zfr_atomic_lookup M count i ki environment first guard numI xi namedI left leftInner leftLaw
  HI HEnv HNumI HFirst HGuard HNamedI HLeft HLeftInner HLeftLaw)as PLeft.
 destruct(sf_relation_total M SFImpl namedJ right)as(rightInner&HRightInner).
 destruct(sf_relation_total M SFImpl guard rightInner)as(rightLaw&HRightLaw).
 pose proof(source_zfr_atomic_lookup M count j kj environment first guard numJ xj namedJ right rightInner rightLaw
  HJ HEnv HNumJ HFirst HGuard HNamedJ HRight HRightInner HRightLaw)as PRight.
 destruct(source_zfr_atomic_operation_shell M member(zeroM M)xi xj(succM M(succM M(succM M i)))(succM M(succM M(succM M j)))
  carrier representative op memCarrier left right atom memRepresentative equiv HOp HCarrier HLeft HRight HAtom HRepresentative HIff)
  as(last&third&second&operationLaw&HLast&HThird&HSecond&HOperationLaw&POperation).
 destruct(sf_relation_total M SFAnd namedI namedJ)as(nums&HNums).
 destruct(sf_relation_total M SFAnd op nums)as(condition&HCondition).
 destruct(sf_relation_total M SFImpl guard memCarrier)as(oldpoint&HOldPoint).
 destruct(sf_relation_total M SFImpl guard equiv)as(newpoint&HNewPoint).
 destruct(sf_relation_total M SFImpl oldpoint newpoint)as(pointmap&HPointMap).
 destruct(sf_relation_total M SFImpl condition pointmap)as(result&HResult).
 exists nums,condition,oldpoint,newpoint,pointmap,result.
 refine(conj HNums(conj HCondition(conj HOldPoint(conj HNewPoint(conj HPointMap(conj HResult _)))))).
 destruct(source_zfr_provable_has_bound M leftLaw PLeft)as(kl&BL).
 destruct(proj1(source_bounded_accept_binary M SFImpl guard leftInner leftLaw kl(or_intror(or_intror eq_refl))HLeftLaw)BL)as(BGuard&BLI).
 destruct(proj1(source_bounded_accept_binary M SFImpl namedI left leftInner kl(or_intror(or_intror eq_refl))HLeftInner)BLI)as(BI&BLeft).
 destruct(source_zfr_provable_has_bound M rightLaw PRight)as(kr&BR).
 destruct(proj1(source_bounded_accept_binary M SFImpl guard rightInner rightLaw kr(or_intror(or_intror eq_refl))HRightLaw)BR)as(_&BRI).
 destruct(proj1(source_bounded_accept_binary M SFImpl namedJ right rightInner kr(or_intror(or_intror eq_refl))HRightInner)BRI)as(BJ&BRight).
 destruct(source_zfr_provable_has_bound M operationLaw POperation)as(ko&BO).
 destruct(proj1(source_bounded_accept_binary M SFImpl op second operationLaw ko(or_intror(or_intror eq_refl))HOperationLaw)BO)as(BOp&BSecond).
 destruct(proj1(source_bounded_accept_binary M SFImpl memCarrier third second ko(or_intror(or_intror eq_refl))HSecond)BSecond)as(BCarrier&BThird).
 destruct(proj1(source_bounded_accept_binary M SFImpl left last third ko(or_intror(or_intror eq_refl))HThird)BThird)as(_&BLast).
 destruct(proj1(source_bounded_accept_binary M SFImpl right equiv last ko(or_intror(or_intror eq_refl))HLast)BLast)as(_&BIff).
 apply(source_zfr_prop_pairs_finite M[(atom_lookup_left,leftLaw);(atom_lookup_right,rightLaw);(atom_operation_profile,operationLaw)]
  atom_point_result source_atomic_point_program[guard;namedI;namedJ;left;right;op;memCarrier;equiv]result).
 - intros f[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]];eexists;eassumption.
 - intros a f[H|[H|[H|[]]]];inversion H;subst a f;split;
   [unfold atom_lookup_left;ap_graph|exact PLeft|unfold atom_lookup_right;ap_graph|exact PRight|unfold atom_operation_profile;ap_graph|exact POperation].
 - unfold atom_point_result,atom_point_condition;ap_graph.
Qed.
Print Assumptions source_zfr_atomic_representation_point.
