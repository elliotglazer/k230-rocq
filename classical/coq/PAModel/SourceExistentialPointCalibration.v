(** The parent existential representation point, normalized from actual
    source-code holes and two explicitly ordered named binders. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SetSchemaConstructors SourceBounded SourceNumeralLift
 SourceEnvironmentCarrierClosure NativeKBundle SourceNamedHoleEvaluation SourceNamedScopes SourceNamedScopeBinding
 SourceRepresentationHeadCalibration SourceRepresentationRecipe SourceIffGraphs.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition existential_point_names(M:Model)(p a:carrier M)i:=match i with 0=>p|_=>a end.
Definition existential_point_template:=NNTAll(CEvar 0)
 (NNTImpl(NNTHole 0)(NNTIff(NNTAtom false(CEvar 0)(CEconst 0))
 (NNTEx(CEvar 1)(NNTAnd(NNTAtom false(CEvar 1)(CEconst 1))(NNTHole 1))))).
Theorem source_existential_point_calibration M p a holes guard theta pair relative result:
 (forall i,exists k,source_bounded M(holes i)k) ->
 zeroM M<>p ->code_numeral M 1<>p ->code_numeral M 1<>a ->p<>a ->
 named_scope_renaming M[p](holes 0)guard ->named_scope_renaming M[a;p](holes 1)theta ->
 sf_relation M SFAnd(code_numeral M(sf_make SFMember 0 3))theta pair ->
 sf_relation M SFEx pair(zeroM M)relative ->
 source_hole_named_evaluation M(existential_point_names M p a)holes existential_point_template result ->
 code_relation M(representation_point_environment guard relative)(E_representation_point(CEvar 0)(CEvar 1))result.
Proof.
 intros BH P0 P1 A1 PA HGuard HTheta HPair HRelative HEval.
 set(member:=code_numeral M(sf_make SFMember 0 1)).
 set(valuemember:=code_numeral M(sf_make SFMember 0 3)).
 pose proof(sf_make_numeral M SFMember 0 1)as HM.
 change(sf_relation M SFMember(zeroM M)(code_numeral M 1)member)in HM.
 pose proof(sf_make_numeral M SFMember 0 3)as HVM.
 change(sf_relation M SFMember(zeroM M)(code_numeral M 3)valuemember)in HVM.
 destruct(source_iff_total M member relative)as(iff&HIff).
 destruct(source_iff_parts M member relative iff HIff)as(lr&rl&HLR&HRL&HI).
 destruct(sf_relation_total M SFImpl guard iff)as(body&HBody).
 destruct(sf_relation_total M SFAll body(zeroM M))as(target&HTarget).
 assert(HMem:scoped_source_hole_evaluation M(existential_point_names M p a)holes[p]
  (NNTAtom false(CEvar 0)(CEconst 0))member).
 { exists p,(zeroM M),(zeroM M),(code_numeral M 1).
   split;[reflexivity|]. split;[reflexivity|]. split;[left;auto|]. split;[|exact HM].
   right. split;[exact P0|]. exists(zeroM M). split;reflexivity. }
 assert(HEx:scoped_source_hole_evaluation M(existential_point_names M p a)holes[p]
  (NNTEx(CEvar 1)(NNTAnd(NNTAtom false(CEvar 1)(CEconst 1))(NNTHole 1)))relative).
 { exists a,pair. split;[reflexivity|]. split;[|exact HRelative].
   exists valuemember,theta. split;[|exact(conj HTheta HPair)].
   exists a,(code_numeral M 1),(zeroM M),(code_numeral M 3).
   split;[reflexivity|]. split;[reflexivity|]. split;[left;auto|]. split;[|exact HVM].
   right. split;[exact A1|]. exists(code_numeral M 2). split;[|reflexivity].
   right. split;[exact P1|]. exists(code_numeral M 1). split;reflexivity. }
 assert(HS:scoped_source_hole_evaluation M(existential_point_names M p a)holes[]existential_point_template target).
 { unfold existential_point_template,NNTIff. cbn[scoped_source_hole_evaluation].
   exists p,body. split;[reflexivity|]. split;[|exact HTarget].
   exists guard,iff. split;[exact HGuard|]. split;[|exact HBody].
   exists lr,rl. split;[|split;[|exact HI]].
   - exists member,relative. exact(conj HMem(conj HEx HLR)).
   - exists relative,member. exact(conj HEx(conj HMem HRL)). }
 pose proof(source_hole_named_scope_empty_exact M(existential_point_names M p a)holes existential_point_template result BH HEval)as HSource.
 rewrite(scoped_source_hole_evaluation_functional M(existential_point_names M p a)holes existential_point_template[]result target HSource HS).
 assert(HIffCode:code_relation M(representation_point_environment guard relative)
  (E_sf_iff(E_sf SFMember(CEconst 0)(CEconst 1))(CEvar 1))iff).
 { unfold E_sf_iff. eapply environment_carrier_code_join;[| |exact HI].
   - eapply environment_carrier_code_join;[|reflexivity|exact HLR]. eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HM].
   - eapply environment_carrier_code_join;[reflexivity| |exact HRL]. eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HM]. }
 unfold E_representation_point. eapply environment_carrier_code_join;[|reflexivity|exact HTarget].
 eapply environment_carrier_code_join;[reflexivity|exact HIffCode|exact HBody].
Qed.
Print Assumptions source_existential_point_calibration.
