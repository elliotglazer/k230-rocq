(** Fixed Def0 witnesses and L membership. No varying source matrix occurs
    in this finite old-library proof package. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase.
From OldZFC Require Import Z_base Z_prim Z_cl Z_L.
From PAModel Require Import SourceLFixed SourceHierarchyOld SourceClosureNumeralsOld SourceEnvFDomainOld.
From Stdlib Require Import Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty |0.
#[local] Existing Instance ZF_pred_sig |0.
Unset Implicit Arguments.
Definition old_local_def_exists_law:form:=∃ Def0 $1 $0.
Theorem old_local_def_exists_proof:old_L_background ⊢C old_local_def_exists_law.
Proof.
 unfold old_local_def_exists_law.
 exact(def_ex_g old_hierarchy_base old_hierarchy_reg old_hierarchy_omega old_closure_axioms $0).
Qed.
Definition old_local_def_unpack_law:form:=Def0 $0 $1 →
 ∃∃((Succ0 $2 $1 ∧Cl $1 $0) ∧
  ∀($0 ∈' $1 →Sub0 $0 $3 →$0 ∈' $4)).
Theorem old_local_def_unpack_proof:old_L_background ⊢C old_local_def_unpack_law.
Proof.
 unfold old_local_def_unpack_law. apply II.
 eapply def_unpack with(A:=$0)(D:=$1).
 - env_domain_bg.
 - env_domain_ctx.
 - intros G1 S0 C Hinc HS HC HD1 HD2.
   fexists S0. fexists C. fsplit;[fsplit;assumption|exact HD2].
Qed.
Definition old_local_L_def_member_law:form:=
 Ord0 $0 →LL $0 $1 →Def0 $1 $2 →$3 ∈' $2 →InL $3.
Theorem old_local_L_def_member_proof:old_L_background ⊢C old_local_L_def_member_law.
Proof.
 unfold old_local_L_def_member_law. apply II,II,II,II.
 eapply L_def_g with(a:=$0)(Y:=$1)(D:=$2)(z:=$3).
 - env_domain_bg.
 - env_domain_reg.
 - env_domain_omega.
 - intros f Hf;repeat first[solve[exact(old_hierarchy_axioms f Hf)]|right].
 - env_domain_ctx.
 - env_domain_ctx.
 - env_domain_ctx.
 - env_domain_ctx.
Qed.
Lemma old_local_selection_operation_point {G:list form}(HG:incl ZF0base G)R s A Y z:
 G ⊢C Op 5 R s A Y ->G ⊢C(z ∈' Y ↔z ∈' A ∧SC R s z).
Proof. intro H. pose proof(sepof_iff HG A Y _ H)as D. finst D z. exact D. Qed.
Definition old_local_selection_operation_law:form:=
 Op 5 $0 $1 $2 $3 →($4 ∈' $3 ↔$4 ∈' $2 ∧SC $0 $1 $4).
Theorem old_local_selection_operation_proof:old_L_background ⊢C old_local_selection_operation_law.
Proof.
 unfold old_local_selection_operation_law. apply II.
 eapply old_local_selection_operation_point.
 - env_domain_bg.
 - env_domain_ctx.
Qed.
Print Assumptions old_local_def_exists_proof.
Print Assumptions old_local_def_unpack_proof.
Print Assumptions old_local_L_def_member_proof.
Print Assumptions old_local_selection_operation_proof.
