(** Finite named head calibration with arbitrary EnvF and source-matrix holes.
    Matrix scoping is independent of the previous-environment witness binder. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SetSchemaConstructors SourceBounded SourceNumeralLift
 SourceEnvironmentCarrierClosure SourceDefinabilityPrimitives NativeKBundle SourceNamedHoleEvaluation
 SourceNamedScopes SourceNamedScopeBinding SourceEnvironmentHeadCalibration SourceRepresentationSuccessorHead SourceRepresentationRecipe SourceIffGraphs.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition NNTIff a b:=NNTAnd(NNTImpl a b)(NNTImpl b a).
Definition representation_head_template:=NNTAll(CEvar 0)
 (NNTImpl(NNTAtom false(CEvar 0)(CEconst 1))
 (NNTAll(CEvar 1)(NNTImpl(NNTEx(CEvar 2)(NNTAnd(NNTHole 0)(NNTHole 1)))
 (NNTIff(NNTAtom false(CEvar 1)(CEconst 0))(NNTHole 2))))).
Theorem source_representation_head_calibration M a e p holes deep relative result:
 (forall i,exists k,source_bounded M(holes i)k) ->
 zeroM M<>a ->code_numeral M 1<>a ->zeroM M<>e ->
 named_scope_renaming M[p;e;a](holes 0)deep ->
 named_scope_renaming M[p;e;a](holes 1)(code_numeral M(sf_encode source_def_extension021)) ->
 named_scope_renaming M[e;a](holes 2)relative ->
 source_hole_named_evaluation M(environment_head_names M a e p)holes representation_head_template result ->
 code_relation M(representation_point_environment deep relative)E_representation_head_point result.
Proof.
 intros BH A0 A1 E0 HDeep HExt HRel HEval.
 set(atom:=code_numeral M(sf_make SFMember 0 2)).
 pose proof(sf_make_numeral M SFMember 0 2)as HA.
 change(sf_relation M SFMember(zeroM M)(code_numeral M 2)atom)in HA.
 destruct(sf_relation_total M SFAnd deep(code_numeral M(sf_encode source_def_extension021)))as(pair&HPair).
 destruct(sf_relation_total M SFEx pair(zeroM M))as(ex&HEx).
 destruct(source_iff_total M atom relative)as(iff&HIff).
 destruct(source_iff_parts M atom relative iff HIff)as(lr&rl&HLR&HRL&HI).
 destruct(sf_relation_total M SFImpl ex iff)as(localbody&HLocal).
 destruct(sf_relation_total M SFAll localbody(zeroM M))as(allenv&HAllEnv).
 destruct(sf_relation_total M SFImpl atom allenv)as(headbody&HHead).
 destruct(sf_relation_total M SFAll headbody(zeroM M))as(target&HTarget).
 assert(HS:scoped_source_hole_evaluation M(environment_head_names M a e p)holes[]representation_head_template target).
 { unfold representation_head_template,NNTIff. cbn[scoped_source_hole_evaluation].
   exists a,headbody. split;[reflexivity|]. split;[|exact HTarget].
   exists atom,allenv. split;[|split;[|exact HHead]].
   - exists a,(code_numeral M 1),(zeroM M),(code_numeral M 2).
     split;[reflexivity|]. split;[reflexivity|]. split;[left;auto|]. split;[|exact HA].
     right. split;[exact A1|]. exists(code_numeral M 1). split;reflexivity.
   - exists e,localbody. split;[reflexivity|]. split;[|exact HAllEnv].
     exists ex,iff. split;[|split;[|exact HLocal]].
     + exists p,pair. split;[reflexivity|]. split;[|exact HEx].
       exists deep,(code_numeral M(sf_encode source_def_extension021)). exact(conj HDeep(conj HExt HPair)).
     + assert(HAtom:exists x y j l,code_relation M(environment_head_names M a e p)(CEvar 1)x /\
        code_relation M(environment_head_names M a e p)(CEconst 0)y /\
        named_scope_index M[e;a]x j /\named_scope_index M[e;a]y l /\sf_relation M SFMember j l atom).
       { exists e,(zeroM M),(zeroM M),(code_numeral M 2).
         split;[reflexivity|]. split;[reflexivity|]. split;[left;auto|]. split;[|exact HA].
         right. split;[exact E0|]. exists(code_numeral M 1). split;[|reflexivity].
         right. split;[exact A0|]. exists(zeroM M). split;reflexivity. }
       exists lr,rl. split;[|split;[|exact HI]].
       * exists atom,relative. exact(conj HAtom(conj HRel HLR)).
       * exists relative,atom. exact(conj HRel(conj HAtom HRL)). }
 pose proof(source_hole_named_scope_empty_exact M(environment_head_names M a e p)holes representation_head_template result BH HEval)as HSource.
 rewrite(scoped_source_hole_evaluation_functional M(environment_head_names M a e p)holes representation_head_template[]result target HSource HS).
 assert(HIffCode:code_relation M(representation_point_environment deep relative)
  (E_sf_iff(CEconst(sf_make SFMember 0 2))(CEvar 1))iff).
 { unfold E_sf_iff. eapply environment_carrier_code_join;[| |exact HI].
   - eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HLR].
   - eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HRL]. }
 unfold E_representation_head_point.
 eapply environment_carrier_code_join;[|reflexivity|exact HTarget].
 eapply environment_carrier_code_join;[reflexivity| |exact HHead].
 eapply environment_carrier_code_join;[|reflexivity|exact HAllEnv].
 eapply environment_carrier_code_join;[|exact HIffCode|exact HLocal].
 eapply environment_carrier_code_join;[|reflexivity|exact HEx].
 eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HPair].
Qed.
Print Assumptions source_representation_head_calibration.
