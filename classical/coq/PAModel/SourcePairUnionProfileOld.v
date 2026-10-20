(** A fixed pair/union membership law for disjunction representatives. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase.
From OldRegCon Require Import MinZF.
From OldZFC Require Import Z_base Z_prim Z_cl.
From PAModel Require Import SourceLFixed SourceEnvFDomainOld.
From Stdlib Require Import Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty |0.
#[local] Existing Instance ZF_pred_sig |0.
Unset Implicit Arguments.
Lemma old_pair_union_profile {G}(HG:incl ZF0base G)x y p r:
 G ⊢C Pair0 x y p ->G ⊢C Union0 p r ->
 G ⊢C ∀($0 ∈' r`[↑] ↔($0 ∈' x`[↑] ∨$0 ∈' y`[↑])).
Proof.
 intros HP HU. fall e. fsplit.
 - fintro H. fhave HX:(union0_el HG p r e HU H). fex HX z HZ. fdestr HZ HZP HEZ.
   fhave HC:(pair0_el HG x y p z HP HZP). fcases HC H1 H2.
   + fleft. fmem.
   + fright. fmem.
 - fintro H. fcases H H1 H2.
   + exact(union0_in HG p r x e HU(pair0_l HG x y p HP)H1).
   + exact(union0_in HG p r y e HU(pair0_r HG x y p HP)H2).
Qed.
Definition old_pair_union_profile_law:form:=Pair0 $0 $1 $2 →Union0 $2 $3 →
 ∀($0 ∈' $4 ↔($0 ∈' $1 ∨$0 ∈' $2)).
Theorem old_pair_union_profile_proof:old_L_background ⊢C old_pair_union_profile_law.
Proof.
 unfold old_pair_union_profile_law. apply II,II.
 assert(HG:incl ZF0base(Union0 $2 $3::Pair0 $0 $1 $2::old_L_background))by env_domain_bg.
 exact(old_pair_union_profile HG $0 $1 $2 $3 ltac:(env_domain_ctx)ltac:(env_domain_ctx)).
Qed.
Print Assumptions old_pair_union_profile.
Print Assumptions old_pair_union_profile_proof.
