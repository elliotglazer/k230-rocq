(** Fixed actual mathematical facts for the existential representation
    constructor. The matrix formula is absent from these certificates. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase.
From OldZFC Require Import Z_base Z_prim Z_cl.
From PAModel Require Import SourceLFixed SourceHierarchyOld SourceClosureNumeralsOld SourceEnvFDomainOld.
From Stdlib Require Import Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty |0.
#[local] Existing Instance ZF_pred_sig |0.
Unset Implicit Arguments.
Lemma old_projection_operation_point {G:list form}(HG:incl ZF0base G)An child A R e:
 G ⊢C Op 4 An child A R ->G ⊢C e ∈' An ->G ⊢C(e ∈' R ↔PJ child A e).
Proof.
 intros HOp HE. fhave D:(sepof_iff HG An R _ HOp). finst D e. fsplit.
 - fintro H. exact(CE2(iff_l _ _ _ D H)).
 - fintro H. apply(iff_r _ _ _ D). fsplit;assumption.
Qed.
Definition old_projection_operation_law:form:=Op 4 $0 $1 $2 $3 →$4 ∈' $0 →($4 ∈' $3 ↔PJ $1 $2 $4).
Theorem old_projection_operation_proof:old_L_background ⊢C old_projection_operation_law.
Proof.
 unfold old_projection_operation_law. apply II,II. eapply old_projection_operation_point with(An:=$0)(child:=$1)(A:=$2)(R:=$3)(e:=$4).
 - env_domain_bg.
 - env_domain_ctx.
 - env_domain_ctx.
Qed.
Definition old_projection_extension_exists:form:=∃(Ext0 $1 $2 $0).
Theorem old_projection_extension_exists_proof:old_L_background ⊢C old_projection_extension_exists.
Proof.
 unfold old_projection_extension_exists. exact(ext0_ex old_hierarchy_base old_hierarchy_reg old_hierarchy_omega old_closure_axioms $0 $1).
Qed.
Print Assumptions old_projection_operation_proof.
Print Assumptions old_projection_extension_exists_proof.

