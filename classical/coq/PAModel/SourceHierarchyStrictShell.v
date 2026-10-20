(** The exact five-premise LL monotonicity law in literal Ord/LL/raw-subset
    graphs. All names are arbitrary elements of the PA model. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
 SourceHierarchyStrictOld SourceHierarchyStrictFixed SourceHierarchySyntax SourceHierarchyCalibration
 SourceFiniteParameters SourceFiniteNameParameters SourceOrdinalPredicate SourceOrdinalParameterCalibration
 SourceSubsetParameterCalibration SourceRawSubset SourcePropositionalRebase SourceFiniteTelescope
 SourceZFRProvability NumericalInstantiation OldNamedSyntaxBridge SchemaConstructorBounds.
From OldZFC Require Z_base Z_L.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque source_LL_predicate source_ordinal_predicate.
Theorem source_zfr_hierarchy_strict_shell M d e u v:
 exists od oe member ld le inLevel subset pair law,
 numerical_instantiation M(source_ordinal_predicate_code M)d od /\
 numerical_instantiation M(source_ordinal_predicate_code M)e oe /\
 sf_relation M SFMember d e member /\source_LL_instance M d u ld /\source_LL_instance M e v le /\
 sf_relation M SFMember u v inLevel /\source_raw_subset_graph M u v subset /\
 sf_relation M SFAnd inLevel subset pair /\source_finite_telescope M[od;oe;member;ld;le]pair law /\
 source_zfr_provable M law.
Proof.
 set(rho:=fun i=>match i with 0=>d|1=>e|2=>u|_=>v end).
 set(names:=source_finite_parameter_names 4).
 destruct(code_relation_total M source_hierarchy_strict_expression rho)as(law&HLaw).
 pose proof(source_zfr_hierarchy_strict M rho law HLaw)as PLaw.
 unfold source_hierarchy_strict_expression,source_hierarchy_strict_law,old_hierarchy_strict_law in HLaw.
 change(code_relation M rho(E_sf SFImpl
  (source_parameter_expression names(isolated_formula(OldZFC.Z_base.Ord0(@OC.var OB.sig_empty 0))))
  (E_sf SFImpl(source_parameter_expression names(isolated_formula(OldZFC.Z_base.Ord0(@OC.var OB.sig_empty 1))))
   (E_sf SFImpl(E_sf SFMember(CEvar 0)(CEvar 1))
    (E_sf SFImpl(source_parameter_expression names(isolated_formula(OldZFC.Z_L.LL(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 2))))
     (E_sf SFImpl(source_parameter_expression names(isolated_formula(OldZFC.Z_L.LL(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 3))))
      (E_sf SFAnd(E_sf SFMember(CEvar 2)(CEvar 3))
       (source_parameter_expression names(isolated_formula(OldZFC.Z_base.Sub0(@OC.var OB.sig_empty 2)(@OC.var OB.sig_empty 3))))))))))law)in HLaw.
 destruct(schema_expression_split M rho _ _ _ law HLaw)as(od&t1&HOD&HT1&H0).
 destruct(schema_expression_split M rho _ _ _ t1 HT1)as(oe&t2&HOE&HT2&H1).
 destruct(schema_expression_split M rho _ _ _ t2 HT2)as(member&t3&HM&HT3&H2).
 destruct(schema_expression_split M rho _ _ _ t3 HT3)as(ld&t4&HLD&HT4&H3).
 destruct(schema_expression_split M rho _ _ _ t4 HT4)as(le&pair&HLE&HPair&H4).
 destruct(schema_expression_split M rho _ _ _ pair HPair)as(inLevel&subset&HMember&HSubset&HAnd).
 assert(N0:code_relation M rho(names 0)d)by reflexivity.
 assert(N1:code_relation M rho(names 1)e)by reflexivity.
 assert(N2:code_relation M rho(names 2)u)by reflexivity.
 assert(N3:code_relation M rho(names 3)v)by reflexivity.
 exists od,oe,member,ld,le,inLevel,subset,pair,law.
 split;[exact(source_parameter_ordinal_instance M names rho 0 d od N0 HOD)|].
 split;[exact(source_parameter_ordinal_instance M names rho 1 e oe N1 HOE)|].
 split;[exact(proj1(schema_expression_graph M rho SFMember(CEvar 0)(CEvar 1)d e member N0 N1)HM)|].
 split;[exact(source_parameter_LL_instance M names rho 0 2 d u ld N0 N2 HLD)|].
 split;[exact(source_parameter_LL_instance M names rho 1 3 e v le N1 N3 HLE)|].
 split;[exact(proj1(schema_expression_graph M rho SFMember(CEvar 2)(CEvar 3)u v inLevel N2 N3)HMember)|].
 split;[exact(source_parameter_raw_subset M names rho 2 3 u v subset N2 N3 HSubset)|].
 split;[exact HAnd|]. split;[|exact PLaw].
 exists t1. split;[|exact H0]. exists t2. split;[|exact H1].
 exists t3. split;[|exact H2]. exists t4. split;[|exact H3].
 exists pair. split;[reflexivity|exact H4].
Qed.
Print Assumptions source_zfr_hierarchy_strict_shell.
