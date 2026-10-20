(** Literal constructor shell of the shared cofinal ordinal-family predicate. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceCofinalGeometry
 SourceFiniteParameters SourceFiniteNameParameters SourceRecursionParameterCalibration SourceOrdinalPredicate
 SourceOrdinalParameterCalibration SourceDomainInstances NumericalInstantiation SourceWFSeparationConstructor SourcePropositionalRebase SchemaConstructorBounds.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.
Theorem source_cofinal_ordinals_shell M K out:
 source_cofinal_ordinals M K out ->exists guard point,
 sf_relation M SFMember(zeroM M)(succM M K)guard /\sf_relation M SFImpl guard(source_ordinal_predicate_code M)point /\sf_relation M SFAll point(zeroM M)out.
Proof.
 intro HO. unfold source_cofinal_ordinals in HO.
 change(code_relation M(fun _=>K)
  (E_sf SFAll(E_sf SFImpl(E_sf SFMember(CEconst 0)(CEadd(CEvar 0)(CEconst 1)))
   (source_parameter_expression(source_parameter_up(source_finite_parameter_names 1))source_ordinal_predicate))(CEconst 0))out)in HO.
 destruct(schema_expression_quantifier_split M _ SFAll _ out HO)as(point&HP&HA).
 destruct(schema_expression_split M _ SFImpl _ _ point HP)as(guard&ordinal&HG&HOrd&HImp).
 pose proof(source_parameter_ordinal_instance M(source_parameter_up(source_finite_parameter_names 1))(fun _=>K)0(zeroM M)ordinal eq_refl HOrd)as HInst.
 pose proof(numerical_instantiation_functional M(source_ordinal_predicate_code M)(zeroM M)ordinal(source_ordinal_predicate_code M)
  HInst(source_domain_instance_zero M(source_ordinal_predicate_code M)(source_ordinal_predicate_bounded M)))as E. subst ordinal.
 assert(HK:code_relation M(fun _=>K)(CEadd(CEvar 0)(CEconst 1))(succM M K)).
 { exact(source_parameter_up_name M(source_finite_parameter_names 1)(fun _=>K)0 K eq_refl). }
 exists guard,point. split;[|auto].
 exact(proj1(schema_expression_graph M(fun _=>K)SFMember(CEconst 0)(CEadd(CEvar 0)(CEconst 1))(zeroM M)(succM M K)guard eq_refl HK)HG).
Qed.
Print Assumptions source_cofinal_ordinals_shell.
