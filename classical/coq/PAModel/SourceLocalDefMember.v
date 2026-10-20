(** Actual L-membership of a Def0 member in the same fixed law context. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceBounded NumericalContexts NumericalSourceFull
 SourceLocalDefinabilityOld SourceLocalDefinabilityFixed SourceLocalDefinabilityContext SourceLocalDefinabilityUnpack SourceLocalParameterReindex
 SourceLocalDefExistence SchemaConstructorBounds SourceFiniteParameters SourceFiniteNameParameters SourceParameterGraphs
 SourceOrdinalParameterCalibration SourceHierarchyCalibration SourceHierarchyWitnessShell SourceHierarchySyntax
 SourceOrdinalPredicate SourceLFixed NumericalInstantiation SourceProofWeakening SourceDerivedRules
 SourceEnvironmentCarrierClosure SourcePropositionalRebase OldNamedSyntaxBridge OldFullNDSourceBridge.
From OldZFC Require Z_base Z_cl Z_L.
From Undecidability.FOL Require Import Syntax.Bounded Syntax.Facts Sets.minZF.
From Stdlib Require Import Lia.
Open Scope minZFsyn.
Unset Implicit Arguments.
Local Opaque source_LL_predicate source_ordinal_predicate source_L_domain.
Definition local_def_member_names {A}(ordinal carrier definables selected:A)i:=
 match i with 0=>ordinal|1=>carrier|2=>definables|_=>selected end.
Definition local_def_member_sigma i:sf_term:=match i with 0=>$1|_=>$2 end.
Theorem source_full_local_def_member M fb fc fn gb gc gn d carrier definables selected ordinal level predicate member inL k:
 source_local_fixed_context M fb fc fn ->context_included M fb fc fn gb gc gn ->context_bounded M gb gc gn k ->
 numerical_instantiation M(source_ordinal_predicate_code M)d ordinal ->source_LL_instance M d carrier level ->
 code_relation M(local_def_names carrier definables)source_local_def_predicate_expression predicate ->
 sf_relation M SFMember selected definables member ->numerical_instantiation M(source_L_domain_code M)selected inL ->
 source_full_prv M gb gc gn ordinal ->source_full_prv M gb gc gn level ->
 source_full_prv M gb gc gn predicate ->source_full_prv M gb gc gn member ->source_full_prv M gb gc gn inL.
Proof.
 intros HF HI HB HO HL HD HM HIn PO PL PD PM.
 set(rho:=local_def_member_names d carrier definables selected).
 set(names:=source_finite_parameter_names 4).
 destruct(code_relation_total M source_local_L_def_member_expression rho)as(law&HG).
 pose proof(source_full_local_fixed_instance M fb fc fn 2 rho law HF ltac:(lia)HG)as PF.
 unfold source_local_L_def_member_expression,source_local_L_def_member_law,old_local_L_def_member_law in HG.
 change(code_relation M rho(E_sf SFImpl
  (source_parameter_expression names(isolated_formula(OldZFC.Z_base.Ord0(@OC.var OB.sig_empty 0))))
  (E_sf SFImpl(source_parameter_expression names(isolated_formula(OldZFC.Z_L.LL(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1))))
   (E_sf SFImpl(source_parameter_expression names(isolated_formula(OldZFC.Z_cl.Def0(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2))))
    (E_sf SFImpl(E_sf SFMember(names 3)(names 2))
     (source_parameter_expression names(isolated_formula(OldZFC.Z_L.InL(@OC.var OB.sig_empty 3))))))))law)in HG.
 destruct(schema_expression_split M rho _ _ _ law HG)as(o&t1&HG0&HGT1&HI0).
 destruct(schema_expression_split M rho _ _ _ t1 HGT1)as(l&t2&HGL&HGT2&HI1).
 destruct(schema_expression_split M rho _ _ _ t2 HGT2)as(p&t3&HGD&HGT3&HI2).
 destruct(schema_expression_split M rho _ _ _ t3 HGT3)as(m&il&HGM&HGI&HI3).
 assert(EO:o=ordinal).
 { exact(numerical_instantiation_functional M(source_ordinal_predicate_code M)d o ordinal
   (source_parameter_ordinal_instance M names rho 0 d o eq_refl HG0)HO). }
 assert(EL:l=level).
 { exact(source_LL_instance_functional M d carrier l level
   (source_parameter_LL_instance M names rho 0 1 d carrier l eq_refl eq_refl HGL)HL). }
 assert(EP:p=predicate).
 { assert(HGD':code_relation M rho(source_parameter_expression names
    (isolated_formula(OldZFC.Z_cl.Def0(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2))))predicate).
   { change(code_relation M rho(source_parameter_expression names(source_local_def_predicate[local_def_member_sigma]))predicate).
     apply(source_local_parameter_reindex M 2 source_local_def_predicate names local_def_member_sigma rho
      (local_def_names carrier definables)predicate).
     - exact source_local_def_predicate_bound.
     - intros[|[|i]]HI';try lia;reflexivity.
     - exact HD. }
   exact(code_relation_functional M _ rho p predicate HGD HGD'). }
 assert(EM:m=member).
 { apply(sf_relation_functional M SFMember selected definables m member);[|exact HM].
   exact(proj1(schema_expression_graph M rho SFMember(names 3)(names 2)selected definables m eq_refl eq_refl)HGM). }
 assert(EI:il=inL).
 { exact(numerical_instantiation_functional M(source_L_domain_code M)selected il inL
   (source_parameter_L_instance M names rho 3 selected il eq_refl HGI)HIn). }
 subst o l p m il.
 pose proof(source_full_prv_weaken_bounded M fb fc fn gb gc gn law k PF HI HB)as PF'.
 pose proof(source_full_modus_ponens M gb gc gn ordinal t1 law HI0 PF' PO)as P1.
 pose proof(source_full_modus_ponens M gb gc gn level t2 t1 HI1 P1 PL)as P2.
 pose proof(source_full_modus_ponens M gb gc gn predicate t3 t2 HI2 P2 PD)as P3.
 exact(source_full_modus_ponens M gb gc gn member inL t3 HI3 P3 PM).
Qed.
Print Assumptions source_full_local_def_member.
