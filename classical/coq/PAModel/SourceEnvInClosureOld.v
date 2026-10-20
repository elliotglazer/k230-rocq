(** Fixed mathematical environment-extension witness in the closure C.
    Only the finite Ext0 operation occurs here, not an arbitrary formula. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase.
From OldZFC Require Import Z_base Z_prim Z_cl.
From PAModel Require Import SourceLFixed SourceHierarchyOld SourceClosureNumeralsOld SourceEnvFDomainOld.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
#[local] Existing Instance sig_empty |0.
#[local] Existing Instance ZF_pred_sig |0.
Unset Implicit Arguments.
Lemma old_env_in_closure_extension {G:list form}(HG:incl ZF0base G)(HR:In ax_reg' G)
 (HOm:In ax_om' G)(HC:incl Ax_cl G) A S0 C e x:
 G ⊢C Succ0 A S0 ->G ⊢C Cl S0 C ->G ⊢C e ∈' C ->G ⊢C x ∈' A ->
 G ⊢C ∃($0 ∈' C`[↑] ∧Ext0 e`[↑] x`[↑] $0).
Proof.
 intros HS HCl He Hx.
 fhave Hv:(clA_el HG HR HOm HC A S0 C x HS HCl Hx).
 fobtain(cl_op_g HG HR HOm HC 0 S0 C e e e ltac:(lia) HCl He He He)as p1 Hp1.
 fdestr Hp1 Hp11 Hp12.
 fobtain(cl_op_g HG HR HOm HC 0 S0 C x x x ltac:(lia) HCl Hv Hv Hv)as p2 Hp2.
 fdestr Hp2 Hp21 Hp22.
 fobtain(cl_op_g HG HR HOm HC 3 S0 C p1 p2 p2 ltac:(lia) HCl Hp11 Hp21 Hp21)as Tt HT.
 fdestr HT HT1 HT2.
 fobtain(cl_op_g HG HR HOm HC 1 S0 C Tt Tt Tt ltac:(lia) HCl HT1 HT1 HT1)as z Hz.
 fdestr Hz Hz1 Hz2.
 fobtain(ext0_ex HG HR HOm HC e x)as z0 Hz0.
 fassert Hz0T:(z0 ∈' Tt).
 { pose proof(CE2 HT2)as H3. finst H3 e. fmp H3(pair0_l HG e e p1 Hp12).
   finst H3 x. fmp H3(pair0_l HG x x p2 Hp22). fex H3 y Hy. fdestr Hy Hy1 Hy2.
   fhave E:(ext0_unique HG HR HOm HC e x y z0 Hy2 Hz0). fmem. }
 fassert E:(z0 ≡' z).
 { apply(ext_rule HG);unfold sub';fall w;fintro Hw.
   - exact(union0_in HG Tt z z0 w Hz2 Hz0T Hw).
   - fhave H:(union0_el HG Tt z w Hz2 Hw). fex H y Hy. fdestr Hy Hy1 Hy2.
     pose proof(CE1 HT2)as H3. finst H3 y. fmp H3 Hy1. fex H3 e1 He1. fdestr He1 He11 He12.
     fex He12 v1 Hv1. fdestr Hv1 Hv11 Hv12.
     fhave E1:(pair0_el HG e e p1 e1 Hp12 He11).
     fhave E2:(pair0_el HG x x p2 v1 Hp22 Hv11).
     fassert E1':(e1 ≡' e). { fcases E1 A1 A2;assumption. }
     fassert E2':(v1 ≡' x). { fcases E2 A1 A2;assumption. }
     frew_in E1' (Ext0 $0 v1`[↑] y`[↑]) Hv12.
     frew_in E2' (Ext0 e`[↑] $0 y`[↑]) Hv12.
     fhave E3:(ext0_unique HG HR HOm HC e x y z0 Hv12 Hz0). fmem. }
 frew_in E (Ext0 e`[↑] x`[↑] $0) Hz0.
 fexists z. fsplit;assumption.
Qed.
Definition old_env_in_closure_extension_law:form:=
 Succ0 $0 $1 →Cl $1 $2 →$3 ∈' $2 →$4 ∈' $0 →∃($0 ∈' $3 ∧Ext0 $4 $5 $0).
Theorem old_env_in_closure_extension_proof:old_L_background ⊢C old_env_in_closure_extension_law.
Proof.
 unfold old_env_in_closure_extension_law. apply II,II,II,II.
 eapply old_env_in_closure_extension with(A:=$0)(S0:=$1)(C:=$2)(e:=$3)(x:=$4);
 [env_domain_bg|env_domain_reg|env_domain_omega|env_domain_cl|env_domain_ctx|env_domain_ctx|env_domain_ctx|env_domain_ctx].
Qed.
Print Assumptions old_env_in_closure_extension_proof.
