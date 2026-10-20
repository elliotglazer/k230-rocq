(** The L-above theorem with its exact ordinal-subset projection. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes NumericalInstantiation
  SourceHierarchyWitnessShell SourceSubsetParameterCalibration SourceRawSubset SourceHierarchySyntax SourceHierarchyCalibration SourceHierarchyWitnessFixed SourceHierarchyWitnessOld
  SourceFiniteParameters SourceFiniteNameParameters SourceFiniteParameterComposition SourceUnaryParameters
  SourceOrdinalPredicate SourceOrdinalParameterCalibration SourceOrdinalMemberShell
  SourceLFixed SourceZFRProvability SourcePropositionalRebase OldNamedSyntaxBridge OldFullNDSourceBridge SubstitutionSource.
From OldZFC Require Z_L.
Unset Implicit Arguments.
Local Opaque source_LL_predicate source_ordinal_predicate source_L_domain.

Theorem source_zfr_hierarchy_above_subset_shell M y g :
  exists ly og exD bodyD bodyY od subset pair level inner member tail law,
    source_hierarchy_above_shell M y g ly og exD bodyD bodyY od subset pair level inner member tail law /\
    source_raw_subset_graph M(succM M(succM M g))(code_numeral M 1)subset /\source_zfr_provable M law.
Proof.
  set(rho:=fun i=>match i with 0=>y|_=>g end).
  set(names:=source_finite_parameter_names 4).
  set(up1:=source_parameter_up names).
  set(up2:=source_parameter_up up1).
  destruct(code_relation_total M source_hierarchy_above_expression rho) as(law&HG).
  pose proof(source_zfr_hierarchy_above M rho law HG) as PLaw.
  unfold source_hierarchy_above_expression,source_hierarchy_above_law,old_hierarchy_above_law in HG.
  change(code_relation M rho(E_sf SFImpl
    (source_parameter_expression names(isolated_formula(OldZFC.Z_L.InL(@OC.var OB.sig_empty 0))))
    (E_sf SFImpl(source_parameter_expression names(isolated_formula(OldZFC.Z_base.Ord0(@OC.var OB.sig_empty 1))))
      (E_sf SFEx(E_sf SFEx(E_sf SFAnd
        (E_sf SFAnd(E_sf SFAnd
          (source_parameter_expression up2(isolated_formula(OldZFC.Z_base.Ord0(@OC.var OB.sig_empty 1))))
          (source_parameter_expression up2(isolated_formula(OldZFC.Z_base.Sub0(@OC.var OB.sig_empty 3)(@OC.var OB.sig_empty 1)))))
          (source_parameter_expression up2(isolated_formula(OldZFC.Z_L.LL(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 0)))))
        (E_sf SFMember(up2 2)(up2 0)))(CEconst 0))(CEconst 0)))) law) in HG.
  destruct(schema_expression_split M rho _ _ _ law HG) as(ly&tail&HLY&HTail&H0).
  destruct(schema_expression_split M rho _ _ _ tail HTail) as(og&exD&HOG&HExD&H1).
  destruct(schema_expression_split M rho SFEx _ (CEconst 0) exD HExD) as(bodyD&unused&HBodyD&HU&H2).
  change(unused=zeroM M) in HU. subst unused.
  destruct(schema_expression_split M rho SFEx _ (CEconst 0) bodyD HBodyD) as(bodyY&unused&HBodyY&HU&H3).
  change(unused=zeroM M) in HU. subst unused.
  destruct(schema_expression_split M rho _ _ _ bodyY HBodyY) as(inner&member&HInner&HMember&H4).
  destruct(schema_expression_split M rho _ _ _ inner HInner) as(pair&level&HPair&HLevel&H5).
  destruct(schema_expression_split M rho _ _ _ pair HPair) as(od&subset&HOD&HSubset&H6).
  assert(N0:code_relation M rho(names 0)y) by reflexivity.
  assert(N1:code_relation M rho(names 1)g) by reflexivity.
  assert(U0:code_relation M rho(up2 0)(zeroM M)) by reflexivity.
  assert(U1:code_relation M rho(up2 1)(code_numeral M 1)).
  { exact(source_code_successor_graph M rho(CEconst 0)(zeroM M) eq_refl). }
  assert(U2:code_relation M rho(up2 2)(succM M(succM M y))).
  { apply(source_code_successor_graph M rho(up1 1)(succM M y)).
    exact(source_code_successor_graph M rho(names 0)y N0). }
  assert(U3:code_relation M rho(up2 3)(succM M(succM M g))).
  { apply(source_code_successor_graph M rho(up1 2)(succM M g)).
    exact(source_code_successor_graph M rho(names 1)g N1). }
  pose proof(source_parameter_raw_subset M up2 rho 3 1(succM M(succM M g))
    (code_numeral M 1)subset U3 U1 HSubset) as HSubsetGraph.
  exists ly,og,exD,bodyD,bodyY,od,subset,pair,level,inner,member,tail,law.
  split;[|split;[exact HSubsetGraph|exact PLaw]].
  split;[exact(source_parameter_L_instance M names rho 0 y ly N0 HLY)|].
  split;[exact(source_parameter_ordinal_instance M names rho 1 g og N1 HOG)|].
  split;[exact(source_parameter_ordinal_instance M up2 rho 1(code_numeral M 1)od U1 HOD)|].
  split;[exact(source_parameter_LL_instance M up2 rho 1 0(code_numeral M 1)(zeroM M)level U1 U0 HLevel)|].
  split;[exact(proj1(substitution_source_constructor_graph M rho SFMember(up2 2)(up2 0)
    (succM M(succM M y))(zeroM M)member U2 U0)HMember)|].
  repeat split;assumption.
Qed.


Print Assumptions source_zfr_hierarchy_above_subset_shell.
