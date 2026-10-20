(** Fixed AI/AE evaluation from two literal application lookup profiles.
    The internally varying environment length does not occur in these laws. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase.
From OldZFC Require Import Z_base Z_prim Z_cl.
From PAModel Require Import SourceLFixed SourceHierarchyOld SourceClosureNumeralsOld.
From Stdlib Require Import Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty |0.
#[local] Existing Instance ZF_pred_sig |0.
Unset Implicit Arguments.

Definition old_atom_app_profile e i a:form:=∀(App0 e`[↑] i`[↑] $0 ↔$0 ≡' a`[↑]).
Lemma old_atom_app_profile_use {G:list form} e i a u :G ⊢C old_atom_app_profile e i a ->
 G ⊢C App0 e i u ↔u ≡' a.
Proof. intro H. unfold old_atom_app_profile in H. finst H u. exact H. Qed.

Lemma old_atom_ai_lookup {G:list form}(HG:incl ZF0base G)(HR:In ax_reg' G)(HOm:In ax_om' G)(HC:incl Ax_cl G)
 e xi xj a b :G ⊢C old_atom_app_profile e xi a ->G ⊢C old_atom_app_profile e xj b ->
 G ⊢C AI xi xj e ↔a ∈' b.
Proof.
 intros HLeft HRight. fsplit.
 - fintro H. unfold AI in H. fex H p Hp. fdestr Hp Hp1 Hp2. fex Hp2 s Hs. fdestr Hs Hs1 Hs2.
   fex Hs2 t Ht. fdestr Ht Ht1 Ht2. fdestr Ht2 Hop Hq. fex Hq p' Hp'. fdestr Hp' Hp'1 Hp'2.
   fex Hp'2 s' Hs'. fdestr Hs' Hs'1 Hs'2. fex Hs'2 t' Ht'. fdestr Ht' Ht'1 Ht'2. fdestr Ht'2 Hop' Htt.
   fhave A1:(u_app0_intro HG HR HOm HC e xi t p Hop Hp1).
   fhave E1:(iff_l _ _ _(old_atom_app_profile_use e xi a t HLeft)A1).
   fhave A2:(u_app0_intro HG HR HOm HC e xj t' p' Hop' Hp'1).
   fhave E2:(iff_l _ _ _(old_atom_app_profile_use e xj b t' HRight)A2).
   exact(elem_cong HG t t' a b E1 E2 Htt).
 - fintro H.
   fhave A1:(iff_r _ _ _(old_atom_app_profile_use e xi a a HLeft)(eq_refl' HG a)).
   fhave A2:(iff_r _ _ _(old_atom_app_profile_use e xj b b HRight)(eq_refl' HG b)).
   unfold App0 in A1,A2. fex A1 p Hp. fdestr Hp Hp1 Hp2. fex A2 p' Hp'. fdestr Hp' Hp'1 Hp'2.
   fhave C1:(op0_c2 HG xi a p Hp2). fex C1 s Hs. fdestr Hs Hs1 Hs2.
   fhave C2:(op0_c2 HG xj b p' Hp'2). fex C2 s' Hs'. fdestr Hs' Hs'1 Hs'2.
   unfold AI. fexists p. fsplit;[exact Hp1|]. fexists s. fsplit;[exact Hs1|]. fexists a. fsplit;[exact Hs2|].
   fsplit;[exact Hp2|]. fexists p'. fsplit;[exact Hp'1|]. fexists s'. fsplit;[exact Hs'1|].
   fexists b. fsplit;[exact Hs'2|]. fsplit;[exact Hp'2|exact H].
Qed.

Lemma old_atom_ae_lookup {G:list form}(HG:incl ZF0base G)(HR:In ax_reg' G)(HOm:In ax_om' G)(HC:incl Ax_cl G)
 e xi xj a b :G ⊢C old_atom_app_profile e xi a ->G ⊢C old_atom_app_profile e xj b ->
 G ⊢C AE xi xj e ↔a ≡' b.
Proof.
 intros HLeft HRight. fsplit.
 - fintro H. unfold AE in H. fex H p Hp. fdestr Hp Hp1 Hp2. fex Hp2 s Hs. fdestr Hs Hs1 Hs2.
   fex Hs2 t Ht. fdestr Ht Ht1 Ht2. fdestr Ht2 Hop Hq. fex Hq p' Hp'. fdestr Hp' Hp'1 Hp'2.
   fex Hp'2 s' Hs'. fdestr Hs' Hs'1 Hs'2. fex Hs'2 t' Ht'. fdestr Ht' Ht'1 Ht'2. fdestr Ht'2 Hop' Htt.
   fhave A1:(u_app0_intro HG HR HOm HC e xi t p Hop Hp1).
   fhave E1:(iff_l _ _ _(old_atom_app_profile_use e xi a t HLeft)A1).
   fhave A2:(u_app0_intro HG HR HOm HC e xj t' p' Hop' Hp'1).
   fhave E2:(iff_l _ _ _(old_atom_app_profile_use e xj b t' HRight)A2).
   feq.
 - fintro H.
   fhave A1:(iff_r _ _ _(old_atom_app_profile_use e xi a a HLeft)(eq_refl' HG a)).
   fhave A2:(iff_r _ _ _(old_atom_app_profile_use e xj b b HRight)(eq_refl' HG b)).
   unfold App0 in A1,A2. fex A1 p Hp. fdestr Hp Hp1 Hp2. fex A2 p' Hp'. fdestr Hp' Hp'1 Hp'2.
   fhave C1:(op0_c2 HG xi a p Hp2). fex C1 s Hs. fdestr Hs Hs1 Hs2.
   fhave C2:(op0_c2 HG xj b p' Hp'2). fex C2 s' Hs'. fdestr Hs' Hs'1 Hs'2.
   unfold AE. fexists p. fsplit;[exact Hp1|]. fexists s. fsplit;[exact Hs1|]. fexists a. fsplit;[exact Hs2|].
   fsplit;[exact Hp2|]. fexists p'. fsplit;[exact Hp'1|]. fexists s'. fsplit;[exact Hs'1|].
   fexists b. fsplit;[exact Hs'2|]. fsplit;[exact Hp'2|exact H].
Qed.

Definition old_atom_ai_lookup_law:form:=old_atom_app_profile $0 $1 $3 →old_atom_app_profile $0 $2 $4 →(AI $1 $2 $0 ↔$3 ∈' $4).
Definition old_atom_ae_lookup_law:form:=old_atom_app_profile $0 $1 $3 →old_atom_app_profile $0 $2 $4 →(AE $1 $2 $0 ↔$3 ≡' $4).
Theorem old_atom_ai_lookup_proof:old_L_background ⊢C old_atom_ai_lookup_law.
Proof.
 unfold old_atom_ai_lookup_law. apply II,II. eapply old_atom_ai_lookup.
 - intros ax H. do 2 right. exact(old_hierarchy_base ax H).
 - do 2 right. exact old_hierarchy_reg.
 - do 2 right. exact old_hierarchy_omega.
 - intros ax H. do 2 right. exact(old_closure_axioms ax H).
 - apply Ctx. right. now left.
 - apply Ctx. now left.
Qed.
Theorem old_atom_ae_lookup_proof:old_L_background ⊢C old_atom_ae_lookup_law.
Proof.
 unfold old_atom_ae_lookup_law. apply II,II. eapply old_atom_ae_lookup.
 - intros ax H. do 2 right. exact(old_hierarchy_base ax H).
 - do 2 right. exact old_hierarchy_reg.
 - do 2 right. exact old_hierarchy_omega.
 - intros ax H. do 2 right. exact(old_closure_axioms ax H).
 - apply Ctx. right. now left.
 - apply Ctx. now left.
Qed.
Print Assumptions old_atom_ai_lookup_proof.
Print Assumptions old_atom_ae_lookup_proof.
