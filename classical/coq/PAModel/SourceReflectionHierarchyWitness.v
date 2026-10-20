(** The actual fixed hierarchy witness needed by PH_from: the smaller
    hierarchy exists and is a subset of the target hierarchy. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase.
From OldRegCon Require Import MinZF.
From OldZFC Require Import Z_base Z_prim Z_L.
From PAModel Require Import SourceLFixed SourceHierarchyOld SourceRecursionFactsOld.
From Stdlib Require Import Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty|0.
#[local] Existing Instance ZF_pred_sig|0.
Unset Implicit Arguments.

Definition old_reflection_hierarchy_witness_law:form:=
  Ord0 $0 → Ord0 $1 → Sub0 $0 $1 → LL $1 $2 →
  ∃ (LL $1 $0 ∧ Sub0 $0 $3).

Lemma old_reflection_hierarchy_witness {G}(HG:incl ZF0base G)
  (HR:In ax_reg' G)(HOm:In ax_om' G)(HL:incl Ax_L G)w beta Lb:
  G ⊢C Ord0 w ->G ⊢C Ord0 beta ->G ⊢C Sub0 w beta ->G ⊢C LL beta Lb ->
  G ⊢C ∃(LL w`[↑] $0 ∧Sub0 $0 Lb`[↑]).
Proof.
  intros Hw Hb HSub HLb.
  pose proof(LL_ex_g HG HR HOm HL w Hw)as HEx.
  fex HEx Y HY. fexists Y. fsplit;[exact HY|].
  eapply LL_sub_g with(a:=beta)(b:=w)(Ya:=Lb)(Yb:=Y);
    [exact HG|exact HR|exact HOm|exact HL|
     exact Hb|exact Hw|exact HSub|exact HLb|exact HY].
Qed.

Theorem old_reflection_hierarchy_witness_proof:
  old_L_background ⊢C old_reflection_hierarchy_witness_law.
Proof.
  unfold old_reflection_hierarchy_witness_law. do 4 apply II.
  eapply old_reflection_hierarchy_witness with(w:=$0)(beta:=$1)(Lb:=$2).
  - recursion_fixed_background.
  - do 4 right. exact old_hierarchy_reg.
  - do 4 right. exact old_hierarchy_omega.
  - intros a HA. do 4 right. exact(old_hierarchy_axioms a HA).
  - recursion_fixed_context.
  - recursion_fixed_context.
  - recursion_fixed_context.
  - recursion_fixed_context.
Qed.

Print Assumptions old_reflection_hierarchy_witness_proof.

From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  OldNamedSyntaxBridge OldZFRProofLift SourceLNonempty SourceFiniteParameters SourceFiniteNameParameters
  SourceZFRProvability SourceDescriptorProvability SourceSetTheoryDescriptors
  SourceOrdinalPredicate SourceOrdinalParameterCalibration SourceSubsetParameterCalibration
  SourceRawSubset SourceHierarchySyntax SourceHierarchyCalibration SourcePropositionalRebase
  SourceFiniteTelescope NumericalInstantiation NumericalSourceFull.
Local Opaque source_LL_predicate source_ordinal_predicate.

Definition source_reflection_hierarchy_witness_expression:=
  source_parameter_expression(source_finite_parameter_names 3)
    (isolated_formula old_reflection_hierarchy_witness_law).

Theorem source_zfr_reflection_hierarchy_witness M rho out:
  code_relation M rho source_reflection_hierarchy_witness_expression out ->
  source_zfr_provable M out.
Proof.
  intro HO. apply(proj1(source_zfr_descriptor_provable M out)).
  apply(source_descriptor_finite_parameter_proof M ZFRSourceDescriptor
    (isolated_formula old_reflection_hierarchy_witness_law)3 rho out).
  - apply(proj2(source_zfr_descriptor_provable M _)).
    exact(finite_old_zfr_proof_lift M old_L_background old_reflection_hierarchy_witness_law
      old_L_background_valid old_reflection_hierarchy_witness_proof).
  - exact HO.
Qed.

Theorem source_zfr_reflection_hierarchy_witness_shell M w beta Lb:
  exists ow ob subset lb lw included body ex law,
    numerical_instantiation M(source_ordinal_predicate_code M)w ow /\
    numerical_instantiation M(source_ordinal_predicate_code M)beta ob /\
    source_raw_subset_graph M w beta subset /\source_LL_instance M beta Lb lb /\
    source_LL_instance M(succM M w)(zeroM M)lw /\
    source_raw_subset_graph M(zeroM M)(succM M Lb)included /\
    sf_relation M SFAnd lw included body /\sf_relation M SFEx body(zeroM M)ex /\
    source_finite_telescope M(cons ow(cons ob(cons subset(cons lb nil))))ex law /\source_zfr_provable M law.
Proof.
  set(rho:=fun i=>match i with 0=>w|1=>beta|_=>Lb end).
  set(names:=source_finite_parameter_names 3).
  destruct(code_relation_total M source_reflection_hierarchy_witness_expression rho)as(law&HLaw).
  pose proof(source_zfr_reflection_hierarchy_witness M rho law HLaw)as PLaw.
  change(code_relation M rho
    (E_sf SFImpl(source_parameter_expression names(isolated_formula(OldZFC.Z_base.Ord0(@OC.var OB.sig_empty 0))))
     (E_sf SFImpl(source_parameter_expression names(isolated_formula(OldZFC.Z_base.Ord0(@OC.var OB.sig_empty 1))))
      (E_sf SFImpl(source_parameter_expression names(isolated_formula(OldZFC.Z_base.Sub0(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1))))
       (E_sf SFImpl(source_parameter_expression names(isolated_formula(OldZFC.Z_L.LL(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2))))
        (E_sf SFEx(E_sf SFAnd
          (source_parameter_expression(source_parameter_up names)(isolated_formula(OldZFC.Z_L.LL(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 0))))
          (source_parameter_expression(source_parameter_up names)(isolated_formula(OldZFC.Z_base.Sub0(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 3)))))
          (CEconst 0))))))law)in HLaw.
  destruct(schema_expression_split M rho SFImpl _ _ law HLaw)as(ow&t1&HOW&HT1&HI0).
  destruct(schema_expression_split M rho SFImpl _ _ t1 HT1)as(ob&t2&HOB&HT2&HI1).
  destruct(schema_expression_split M rho SFImpl _ _ t2 HT2)as(subset&t3&HSub&HT3&HI2).
  destruct(schema_expression_split M rho SFImpl _ _ t3 HT3)as(lb&ex&HLb&HEx&HI3).
  destruct(schema_expression_split M rho SFEx _ _ ex HEx)as(body&z&HBody&HZ&HQuant).
  change(z=zeroM M)in HZ. subst z.
  destruct(schema_expression_split M rho SFAnd _ _ body HBody)as(lw&included&HLw&HIncluded&HAnd).
  assert(N0:code_relation M rho(names 0)w)by reflexivity.
  assert(N1:code_relation M rho(names 1)beta)by reflexivity.
  assert(N2:code_relation M rho(names 2)Lb)by reflexivity.
  assert(U0:code_relation M rho(source_parameter_up names 0)(zeroM M))by reflexivity.
  assert(U1:code_relation M rho(source_parameter_up names 1)(succM M w)).
  { exists w,(code_numeral M 1). split;[exact N0|]. split;[reflexivity|exact(Arithmetic.succ_as_add M w)]. }
  assert(U3:code_relation M rho(source_parameter_up names 3)(succM M Lb)).
  { exists Lb,(code_numeral M 1). split;[exact N2|]. split;[reflexivity|exact(Arithmetic.succ_as_add M Lb)]. }
  exists ow,ob,subset,lb,lw,included,body,ex,law.
  split;[exact(source_parameter_ordinal_instance M names rho 0 w ow N0 HOW)|].
  split;[exact(source_parameter_ordinal_instance M names rho 1 beta ob N1 HOB)|].
  split;[exact(source_parameter_raw_subset M names rho 0 1 w beta subset N0 N1 HSub)|].
  split;[exact(source_parameter_LL_instance M names rho 1 2 beta Lb lb N1 N2 HLb)|].
  split;[exact(source_parameter_LL_instance M(source_parameter_up names)rho 1 0(succM M w)(zeroM M)lw U1 U0 HLw)|].
  split;[exact(source_parameter_raw_subset M(source_parameter_up names)rho 0 3(zeroM M)(succM M Lb)included U0 U3 HIncluded)|].
  split;[exact HAnd|]. split;[exact HQuant|]. split;[|exact PLaw].
  exists t1. split;[|exact HI0]. exists t2. split;[|exact HI1].
  exists t3. split;[|exact HI2]. exists ex. split;[reflexivity|exact HI3].
Qed.

Print Assumptions source_zfr_reflection_hierarchy_witness.
Print Assumptions source_zfr_reflection_hierarchy_witness_shell.
