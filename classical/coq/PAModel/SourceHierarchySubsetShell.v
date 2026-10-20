(** Actual hierarchy monotonicity law in literal Ord/LL/subset graphs. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceHierarchySyntax SourceHierarchyCalibration SourceHierarchyFixed SourceHierarchyOld
  SourceFiniteParameters SourceFiniteNameParameters SourceOrdinalPredicate SourceOrdinalParameterCalibration
  SourceSubsetParameterCalibration SourceRawSubset SourcePropositionalRebase SourcePropositionalTemplates
  SourceFunctionalityShells SourceZFRProvability NumericalInstantiation OldNamedSyntaxBridge.
Unset Implicit Arguments.
Local Opaque source_LL_predicate source_ordinal_predicate.

Definition source_hierarchy_subset_environment {A} (od oe subset ld le result:A) i :=
  match i with 0=>od|1=>oe|2=>subset|3=>ld|4=>le|_=>result end.
Definition source_hierarchy_subset_template :=SPTImpl (SPTSlot 0) (SPTImpl (SPTSlot 1)
  (SPTImpl (SPTSlot 2) (SPTImpl (SPTSlot 3) (SPTImpl (SPTSlot 4) (SPTSlot 5))))).
Definition source_hierarchy_subset_shell M d e u v od oe subset ld le result law :=
  numerical_instantiation M (source_ordinal_predicate_code M) d od /\
  numerical_instantiation M (source_ordinal_predicate_code M) e oe /\
  source_raw_subset_graph M d e subset /\source_LL_instance M d u ld /\
  source_LL_instance M e v le /\source_raw_subset_graph M u v result /\
  code_relation M (source_hierarchy_subset_environment od oe subset ld le result)
    (source_prop_expression source_hierarchy_subset_template) law.

Theorem source_zfr_hierarchy_subset_shell M d e u v :exists od oe subset ld le result law,
  source_hierarchy_subset_shell M d e u v od oe subset ld le result law /\source_zfr_provable M law.
Proof.
  set (rho:=fun i=>match i with 0=>d|1=>e|2=>u|_=>v end).
  set (names:=source_finite_parameter_names 4).
  destruct (code_relation_total M source_hierarchy_subset_expression rho) as (law&HLaw).
  pose proof (source_zfr_hierarchy_subset M rho law HLaw) as PLaw.
  unfold source_hierarchy_subset_expression,source_hierarchy_subset_law,old_hierarchy_subset_law in HLaw.
  change (code_relation M rho
    (E_sf SFImpl (source_parameter_expression names (isolated_formula (OldZFC.Z_base.Ord0 (@OC.var OB.sig_empty 0))))
      (E_sf SFImpl (source_parameter_expression names (isolated_formula (OldZFC.Z_base.Ord0 (@OC.var OB.sig_empty 1))))
        (E_sf SFImpl (source_parameter_expression names (isolated_formula (OldZFC.Z_base.Sub0 (@OC.var OB.sig_empty 0) (@OC.var OB.sig_empty 1))))
          (E_sf SFImpl (source_parameter_expression names (isolated_formula (OldZFC.Z_L.LL (@OC.var OB.sig_empty 0) (@OC.var OB.sig_empty 2))))
            (E_sf SFImpl (source_parameter_expression names (isolated_formula (OldZFC.Z_L.LL (@OC.var OB.sig_empty 1) (@OC.var OB.sig_empty 3))))
              (source_parameter_expression names (isolated_formula (OldZFC.Z_base.Sub0 (@OC.var OB.sig_empty 2) (@OC.var OB.sig_empty 3))))))))) law) in HLaw.
  destruct (schema_expression_split M rho _ _ _ law HLaw) as (od&t1&HOD&HT1&H0).
  destruct (schema_expression_split M rho _ _ _ t1 HT1) as (oe&t2&HOE&HT2&H1).
  destruct (schema_expression_split M rho _ _ _ t2 HT2) as (subset&t3&HS&HT3&H2).
  destruct (schema_expression_split M rho _ _ _ t3 HT3) as (ld&t4&HLD&HT4&H3).
  destruct (schema_expression_split M rho _ _ _ t4 HT4) as (le&result&HLE&HResult&H4).
  assert (N0:code_relation M rho (names 0) d) by reflexivity.
  assert (N1:code_relation M rho (names 1) e) by reflexivity.
  assert (N2:code_relation M rho (names 2) u) by reflexivity.
  assert (N3:code_relation M rho (names 3) v) by reflexivity.
  exists od,oe,subset,ld,le,result,law. split;[|exact PLaw].
  split;[exact (source_parameter_ordinal_instance M names rho 0 d od N0 HOD)|].
  split;[exact (source_parameter_ordinal_instance M names rho 1 e oe N1 HOE)|].
  split;[exact (source_parameter_raw_subset M names rho 0 1 d e subset N0 N1 HS)|].
  split;[exact (source_parameter_LL_instance M names rho 0 2 d u ld N0 N2 HLD)|].
  split;[exact (source_parameter_LL_instance M names rho 1 3 e v le N1 N3 HLE)|].
  split;[exact (source_parameter_raw_subset M names rho 2 3 u v result N2 N3 HResult)|].
  unfold source_hierarchy_subset_template,source_prop_expression. functionality_graph.
Qed.

Print Assumptions source_zfr_hierarchy_subset_shell.
