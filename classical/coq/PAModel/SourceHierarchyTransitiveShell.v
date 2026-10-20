(** Literal Ord/LL/member/raw-subset graphs for the hierarchy transitivity law. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceHierarchyTransitiveOld SourceHierarchyTransitiveFixed SourceHierarchySyntax SourceHierarchyCalibration
  SourceFiniteParameters SourceFiniteNameParameters SourceOrdinalPredicate SourceOrdinalParameterCalibration
  SourceSubsetParameterCalibration SourceRawSubset SourcePropositionalRebase SourceZFRProvability
  NumericalInstantiation OldNamedSyntaxBridge SchemaConstructorBounds.
From OldZFC Require Z_base Z_L.
Unset Implicit Arguments.

Theorem source_zfr_hierarchy_element_subset_shell M d Y A :exists ordinal level member subset t2 t1 law,
  numerical_instantiation M(source_ordinal_predicate_code M)d ordinal /\source_LL_instance M d Y level /\
  sf_relation M SFMember A Y member /\source_raw_subset_graph M A Y subset /\
  sf_relation M SFImpl member subset t2 /\sf_relation M SFImpl level t2 t1 /\
  sf_relation M SFImpl ordinal t1 law /\source_zfr_provable M law.
Proof.
  set(rho:=fun i:nat=>match i with 0=>d|1=>Y|_=>A end).
  destruct(code_relation_total M source_hierarchy_element_subset_expression rho) as(law&HLaw).
  pose proof(source_zfr_hierarchy_element_subset M rho law HLaw) as PLaw.
  unfold source_hierarchy_element_subset_expression,source_hierarchy_element_subset_law,old_hierarchy_element_subset_law in HLaw.
  change(code_relation M rho(E_sf SFImpl
    (source_parameter_expression(source_finite_parameter_names 3)(isolated_formula(OldZFC.Z_base.Ord0(@OC.var OB.sig_empty 0))))
    (E_sf SFImpl(source_parameter_expression(source_finite_parameter_names 3)(isolated_formula(OldZFC.Z_L.LL(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1))))
      (E_sf SFImpl(E_sf SFMember(CEvar 2)(CEvar 1))
        (source_parameter_expression(source_finite_parameter_names 3)(isolated_formula(OldZFC.Z_base.Sub0(@OC.var OB.sig_empty 2)(@OC.var OB.sig_empty 1)))))))law) in HLaw.
  destruct(schema_expression_split M rho _ _ _ law HLaw) as(ordinal&t1&HOrd&HT1&H1).
  destruct(schema_expression_split M rho _ _ _ t1 HT1) as(level&t2&HLevel&HT2&H2).
  destruct(schema_expression_split M rho _ _ _ t2 HT2) as(member&subset&HMember&HSubset&H3).
  pose proof(source_parameter_ordinal_instance M(source_finite_parameter_names 3)rho 0 d ordinal eq_refl HOrd) as HO.
  pose proof(source_parameter_LL_instance M(source_finite_parameter_names 3)rho 0 1 d Y level eq_refl eq_refl HLevel) as HL.
  pose proof(proj1(schema_expression_graph M rho SFMember(CEvar 2)(CEvar 1)A Y member eq_refl eq_refl)HMember) as HM.
  pose proof(source_parameter_raw_subset M(source_finite_parameter_names 3)rho 2 1 A Y subset eq_refl eq_refl HSubset) as HS.
  exists ordinal,level,member,subset,t2,t1,law. repeat split;assumption.
Qed.

Print Assumptions source_zfr_hierarchy_element_subset_shell.
