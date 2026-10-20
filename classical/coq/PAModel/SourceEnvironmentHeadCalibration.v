(** The finite head/new-environment/old-environment binder skeleton,
 evaluated on arbitrary internal EnvF and extension-code holes. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceNumeralLift
 SourceEnvironmentCarrierClosure SourceDefinabilityPrimitives NativeKBundle SourceNamedHoleEvaluation
 SourceNamedScopes SourceNamedScopeBinding.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition environment_head_template:=NNTAll(CEvar 0)
 (NNTImpl(NNTAtom false(CEvar 0)(CEconst 1))
 (NNTAll(CEvar 1)(NNTImpl(NNTEx(CEvar 2)(NNTAnd(NNTHole 0)(NNTHole 1)))
 (NNTAtom false(CEvar 1)(CEconst 0))))).
Definition E_environment_head_point:=E_sf SFAll
 (E_sf SFImpl(CEconst(sf_make SFMember 0 2))
 (E_sf SFAll(E_sf SFImpl(E_sf SFEx(E_sf SFAnd(CEvar 0)(CEconst(sf_encode source_def_extension021)))(CEconst 0))
 (CEconst(sf_make SFMember 0 2)))(CEconst 0)))(CEconst 0).
Definition environment_head_names(M:Model)(a e p:carrier M)i:=match i with 0=>a|1=>e|_=>p end.
Theorem source_environment_head_calibration M a e p holes deep result:
 (forall i,exists k,source_bounded M(holes i)k) ->
 zeroM M<>a ->code_numeral M 1<>a ->zeroM M<>e ->
 named_scope_renaming M[p;e;a](holes 0)deep ->
 named_scope_renaming M[p;e;a](holes 1)(code_numeral M(sf_encode source_def_extension021)) ->
 source_hole_named_evaluation M(environment_head_names M a e p)holes environment_head_template result ->
 code_relation M(fun _=>deep)E_environment_head_point result.
Proof.
 intros BH A0 A1 E0 HDeep HExt HEval.
 set(atom:=code_numeral M(sf_make SFMember 0 2)).
 pose proof(sf_make_numeral M SFMember 0 2)as HA.
 change(sf_relation M SFMember(zeroM M)(code_numeral M 2)atom)in HA.
 destruct(sf_relation_total M SFAnd deep(code_numeral M(sf_encode source_def_extension021)))as(pair&HPair).
 destruct(sf_relation_total M SFEx pair(zeroM M))as(ex&HEx).
 destruct(sf_relation_total M SFImpl ex atom)as(localbody&HLocal).
 destruct(sf_relation_total M SFAll localbody(zeroM M))as(allenv&HAllEnv).
 destruct(sf_relation_total M SFImpl atom allenv)as(headbody&HHead).
 destruct(sf_relation_total M SFAll headbody(zeroM M))as(target&HTarget).
 assert(HS:scoped_source_hole_evaluation M(environment_head_names M a e p)holes[]environment_head_template target).
 { unfold environment_head_template. cbn[scoped_source_hole_evaluation].
   exists a,headbody. split;[reflexivity|]. split;[|exact HTarget].
   exists atom,allenv. split;[|split;[|exact HHead]].
   - exists a,(code_numeral M 1),(zeroM M),(code_numeral M 2).
     split;[reflexivity|]. split;[reflexivity|]. split;[left;auto|]. split;[|exact HA].
     right. split;[exact A1|]. exists(code_numeral M 1). split;reflexivity.
   - exists e,localbody. split;[reflexivity|]. split;[|exact HAllEnv].
     exists ex,atom. split;[|split;[|exact HLocal]].
     + exists p,pair. split;[reflexivity|]. split;[|exact HEx].
       exists deep,(code_numeral M(sf_encode source_def_extension021)). exact(conj HDeep(conj HExt HPair)).
     + exists e,(zeroM M),(zeroM M),(code_numeral M 2).
       split;[reflexivity|]. split;[reflexivity|]. split;[left;auto|]. split;[|exact HA].
       right. split;[exact E0|]. exists(code_numeral M 1). split;[|reflexivity].
       right. split;[exact A0|]. exists(zeroM M). split;reflexivity. }
 pose proof(source_hole_named_scope_empty_exact M(environment_head_names M a e p)holes environment_head_template result BH HEval)as HSource.
 rewrite(scoped_source_hole_evaluation_functional M(environment_head_names M a e p)holes environment_head_template[]result target HSource HS).
 unfold E_environment_head_point.
 eapply environment_carrier_code_join;[|reflexivity|exact HTarget].
 eapply environment_carrier_code_join;[reflexivity| |exact HHead].
 eapply environment_carrier_code_join;[|reflexivity|exact HAllEnv].
 eapply environment_carrier_code_join;[|reflexivity|exact HLocal].
 eapply environment_carrier_code_join;[|reflexivity|exact HEx].
 eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HPair].
Qed.
Print Assumptions source_environment_head_calibration.
