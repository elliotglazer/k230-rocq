(** Literal ordinary source law Ord(d)->LL(d,Y)->L(Y). *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes NumericalInstantiation
 SourceLFixed SourceLLevelOld SourceLLevelFixed SourceHierarchySyntax SourceHierarchyCalibration SourceHierarchyWitnessShell
 SourceFiniteParameters SourceFiniteNameParameters SourceOrdinalPredicate SourceOrdinalParameterCalibration
 SourcePropositionalRebase OldNamedSyntaxBridge OldFullNDSourceBridge SourceZFRProvability.
From OldZFC Require Z_base Z_L.
Unset Implicit Arguments.
Local Opaque source_LL_predicate source_ordinal_predicate source_L_domain.
Theorem source_zfr_L_level_shell M d Y:exists ordinal level inL tail law,
 numerical_instantiation M(source_ordinal_predicate_code M)d ordinal /\source_LL_instance M d Y level /\
 numerical_instantiation M(source_L_domain_code M)Y inL /\sf_relation M SFImpl level inL tail /\
 sf_relation M SFImpl ordinal tail law /\source_zfr_provable M law.
Proof.
 set(rho:=fun i:nat=>match i with 0=>d|_=>Y end). set(names:=source_finite_parameter_names 2).
 destruct(code_relation_total M source_L_level_expression rho)as(law&HG).
 pose proof(source_zfr_L_level M rho law HG)as PLaw.
 unfold source_L_level_expression,source_L_level_law,old_L_level_law in HG.
 change(code_relation M rho(E_sf SFImpl
  (source_parameter_expression names(isolated_formula(OldZFC.Z_base.Ord0(@OC.var OB.sig_empty 0))))
  (E_sf SFImpl(source_parameter_expression names(isolated_formula(OldZFC.Z_L.LL(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1))))
   (source_parameter_expression names(isolated_formula(OldZFC.Z_L.InL(@OC.var OB.sig_empty 1))))))law)in HG.
 destruct(schema_expression_split M rho _ _ _ law HG)as(ordinal&tail&HO&HT&HI).
 destruct(schema_expression_split M rho _ _ _ tail HT)as(level&inL&HL&HD&HI').
 exists ordinal,level,inL,tail,law.
 split;[exact(source_parameter_ordinal_instance M names rho 0 d ordinal eq_refl HO)|].
 split;[exact(source_parameter_LL_instance M names rho 0 1 d Y level eq_refl eq_refl HL)|].
 split;[exact(source_parameter_L_instance M names rho 1 Y inL eq_refl HD)|].
 auto 10.
Qed.
Print Assumptions source_zfr_L_level_shell.
