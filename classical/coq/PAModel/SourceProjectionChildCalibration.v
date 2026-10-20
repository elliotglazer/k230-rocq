(** Finite named child-head calibration at an arbitrary representative.
    The representative need only avoid the two binders surrounding its atom. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SetSchemaConstructors SchemaConstructorBounds SourceBounded SourceNumeralLift
 SourceEnvironmentCarrierClosure SourceDefinabilityPrimitives NativeKBundle SourceNamedHoleEvaluation
 SourceNamedScopes SourceNamedScopeBinding SourceRepresentationHeadCalibration SourceProjectionHeadTotal SourceProjectionHeadImage
 SourceRepresentationRecipe SourceIffGraphs.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_projection_child_head_calibration M a e p r holes deep relative result:
 (forall i,exists k,source_bounded M(holes i)k)->
 zeroM M<>a->code_numeral M 1<>a->zeroM M<>e->r<>e->r<>a->
 named_scope_renaming M[p;e;a](holes 0)deep->
 named_scope_renaming M[p;e;a](holes 1)(code_numeral M(sf_encode source_def_extension021))->
 named_scope_renaming M[e;a](holes 2)relative->
 source_hole_named_evaluation M(projection_child_names M a e p r)holes projection_child_template result->
 code_relation M(schema_env3 deep relative(succM M(succM M r)))E_projection_child_head_point result.
Proof.
 intros BH A0 A1 E0 RE RA HDeep HExt HRel HEval.
 set(atom:=code_numeral M(sf_make SFMember 0 2)).
 pose proof(sf_make_numeral M SFMember 0 2)as HA.
 change(sf_relation M SFMember(zeroM M)(code_numeral M 2)atom)in HA.
 destruct(sf_relation_total M SFMember(zeroM M)(succM M(succM M r)))as(childatom&HChild).
 destruct(sf_relation_total M SFAnd deep(code_numeral M(sf_encode source_def_extension021)))as(pair&HPair).
 destruct(sf_relation_total M SFEx pair(zeroM M))as(ex&HEx).
 destruct(source_iff_total M childatom relative)as(iff&HIff).
 destruct(source_iff_parts M childatom relative iff HIff)as(lr&rl&HLR&HRL&HI).
 destruct(sf_relation_total M SFImpl ex iff)as(localbody&HLocal).
 destruct(sf_relation_total M SFAll localbody(zeroM M))as(allenv&HAllEnv).
 destruct(sf_relation_total M SFImpl atom allenv)as(headbody&HHead).
 destruct(sf_relation_total M SFAll headbody(zeroM M))as(target&HTarget).
 assert(HS:scoped_source_hole_evaluation M(projection_child_names M a e p r)holes[]projection_child_template target).
 { unfold projection_child_template,NNTIff. cbn[scoped_source_hole_evaluation].
   exists a,headbody. split;[reflexivity|]. split;[|exact HTarget].
   exists atom,allenv. split;[|split;[|exact HHead]].
   - exists a,(code_numeral M 1),(zeroM M),(code_numeral M 2).
     split;[reflexivity|]. split;[reflexivity|]. split;[left;auto|]. split;[|exact HA].
     right. split;[exact A1|]. exists(code_numeral M 1). split;reflexivity.
   - exists e,localbody. split;[reflexivity|]. split;[|exact HAllEnv].
     exists ex,iff. split;[|split;[|exact HLocal]].
     + exists p,pair. split;[reflexivity|]. split;[|exact HEx].
       exists deep,(code_numeral M(sf_encode source_def_extension021)). exact(conj HDeep(conj HExt HPair)).
     + assert(HAtom:exists x y j l,code_relation M(projection_child_names M a e p r)(CEvar 1)x/\
        code_relation M(projection_child_names M a e p r)(CEvar 3)y/\
        named_scope_index M[e;a]x j/\named_scope_index M[e;a]y l/\sf_relation M SFMember j l childatom).
       { exists e,r,(zeroM M),(succM M(succM M r)).
         split;[reflexivity|]. split;[reflexivity|]. split;[left;auto|]. split;[|exact HChild].
         right. split;[exact RE|]. exists(succM M r). split;[|reflexivity].
         right. split;[exact RA|]. exists r. split;reflexivity. }
       exists lr,rl. split;[|split;[|exact HI]].
       * exists childatom,relative. exact(conj HAtom(conj HRel HLR)).
       * exists relative,childatom. exact(conj HRel(conj HAtom HRL)). }
 pose proof(source_hole_named_scope_empty_exact M(projection_child_names M a e p r)holes projection_child_template result BH HEval)as HSource.
 rewrite(scoped_source_hole_evaluation_functional M(projection_child_names M a e p r)holes projection_child_template[]result target HSource HS).
 set(env:=schema_env3 deep relative(succM M(succM M r))).
 assert(HChildCode:code_relation M env(E_sf SFMember(CEconst 0)(CEvar 2))childatom).
 { exact(proj2(schema_expression_graph M env SFMember(CEconst 0)(CEvar 2)(zeroM M)(succM M(succM M r))childatom eq_refl eq_refl)HChild). }
 assert(HIffCode:code_relation M env(E_sf_iff(E_sf SFMember(CEconst 0)(CEvar 2))(CEvar 1))iff).
 { unfold E_sf_iff. eapply environment_carrier_code_join;[| |exact HI].
   - eapply environment_carrier_code_join;[exact HChildCode|reflexivity|exact HLR].
   - eapply environment_carrier_code_join;[reflexivity|exact HChildCode|exact HRL]. }
 unfold E_projection_child_head_point.
 eapply environment_carrier_code_join;[|reflexivity|exact HTarget].
 eapply environment_carrier_code_join;[reflexivity| |exact HHead].
 eapply environment_carrier_code_join;[|reflexivity|exact HAllEnv].
 eapply environment_carrier_code_join;[|exact HIffCode|exact HLocal].
 eapply environment_carrier_code_join;[|reflexivity|exact HEx].
 eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HPair].
Qed.
Print Assumptions source_projection_child_head_calibration.
