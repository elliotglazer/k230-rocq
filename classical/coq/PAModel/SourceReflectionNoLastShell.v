(** Exact outer shell of the finite no-last predicate. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
 SourceReflectionGeometryPredicates SourceReflectionNoLastNext SourceRecursionParameterCalibration
 SourceFiniteParameters SourceFiniteNameParameters SourceWFSeparationConstructor SourcePropositionalRebase SchemaConstructorBounds.
Unset Implicit Arguments.
Theorem source_reflection_no_last_shell M K out:
 source_reflection_geometry_instance M ReflectionNoLast(fun _=>K)out ->exists guard next point,
 sf_relation M SFMember(zeroM M)(succM M K)guard /\source_reflection_no_last_next M(succM M K)(zeroM M)next /\
 sf_relation M SFImpl guard next point /\sf_relation M SFAll point(zeroM M)out.
Proof.
 intro HO. change(code_relation M(fun _=>K)
  (E_sf SFAll(E_sf SFImpl(E_sf SFMember(CEconst 0)(CEadd(CEvar 0)(CEconst 1)))
   (E_sf SFEx(E_sf SFAnd(E_sf SFMember(CEconst 0)(CEadd(CEadd(CEvar 0)(CEconst 1))(CEconst 1)))
    (E_sf SFMember(CEadd(CEconst 0)(CEconst 1))(CEconst 0)))(CEconst 0)))(CEconst 0))out)in HO.
 destruct(schema_expression_quantifier_split M _ SFAll _ out HO)as(point&HP&HA).
 destruct(schema_expression_split M _ SFImpl _ _ point HP)as(guard&next&HG&HN&HImp).
 destruct(schema_expression_quantifier_split M _ SFEx _ next HN)as(body&HB&HEx).
 destruct(schema_expression_split M _ SFAnd _ _ body HB)as(member&step&HM&HT&HAnd).
 pose proof(source_parameter_up_name M(source_finite_parameter_names 1)(fun _=>K)0 K eq_refl)as HK1.
 pose proof(source_parameter_up_name M(source_parameter_up(source_finite_parameter_names 1))(fun _=>K)1(succM M K)HK1)as HK2.
 pose proof(source_parameter_up_name M(source_parameter_up(source_finite_parameter_names 1))(fun _=>K)0(zeroM M)eq_refl)as HOne.
 exists guard,next,point. split.
 - exact(proj1(schema_expression_graph M(fun _=>K)SFMember(CEconst 0)(CEadd(CEvar 0)(CEconst 1))(zeroM M)(succM M K)guard eq_refl HK1)HG).
 - split;[|auto]. exists member,step,body. split.
   + exact(proj1(schema_expression_graph M(fun _=>K)SFMember(CEconst 0)(CEadd(CEadd(CEvar 0)(CEconst 1))(CEconst 1))(zeroM M)(succM M(succM M K))member eq_refl HK2)HM).
   + split.
     * exact(proj1(schema_expression_graph M(fun _=>K)SFMember(CEadd(CEconst 0)(CEconst 1))(CEconst 0)(code_numeral M 1)(zeroM M)step HOne eq_refl)HT).
     * auto.
Qed.
Print Assumptions source_reflection_no_last_shell.
