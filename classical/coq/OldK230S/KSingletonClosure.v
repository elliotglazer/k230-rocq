(** A raw set of domain objects closed under domain singletons. *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From OldK230S Require Import KP0 KP0Use KPRaw KBase KMarkers KTagged KDPair.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Lemma domain_pair_subst t a b c sg :
  (domain_pair t a b c)[sg] = domain_pair t`[sg] a`[sg] b`[sg] c`[sg].
Proof. psubst domain_pair. Qed.
#[global] Hint Rewrite domain_pair_subst : fsub.
#[global] Arguments domain_pair : simpl never.

(** Output/input are 0/1; parameters are the empty marker and seed object. *)
Definition singleton_closure_matrix : form :=
  ($1 ≡' $2 ∧ $0 ≡' $3) ∨ ($2 ∈' $1 ∧ domain_pair $2 $1 $1 $0).
Lemma singleton_closure_matrix_bounded : fb 4 singleton_closure_matrix.
Proof. unfold singleton_closure_matrix, domain_pair. cbn. lia. Qed.

Definition singleton_closure_profile (t a c : term) : form :=
  (a ∈' c ∧ ∀ ($0 ∈' c`[↑] → t`[↑] ∈' $0)) ∧
  ∀ ($0 ∈' c`[↑] → ∃ ($0 ∈' c`[↑]`[↑] ∧ domain_pair t`[↑]`[↑] $1 $1 $0)).
#[global] Arguments singleton_closure_profile : simpl never.
Lemma singleton_closure_profile_subst t a c sg :
  (singleton_closure_profile t a c)[sg] = singleton_closure_profile t`[sg] a`[sg] c`[sg].
Proof. psubst singleton_closure_profile. Qed.
#[global] Hint Rewrite singleton_closure_profile_subst : fsub.

Lemma singleton_closure_exists G (HB : incl KBase G) t a :
  In (forall_times 3 (kp0 (tagged_matrix true_formula))) G ->
  In (forall_times 2 (kp0 singleton_closure_matrix)) G ->
  G ⊢C raw_empty t -> G ⊢C t ∈' a -> G ⊢C ∃ singleton_closure_profile t`[↑] a`[↑] $0.
Proof.
  intros Hpair Hinst Hempty Hta. pose proof (KBase_eq _ HB) as HE.
  pose proof (kp0_use _ 2 singleton_closure_matrix (t .: a .: var) t
    Hinst singleton_closure_matrix_bounded) as T.
  fex T c HC. fdestr HC Hrequest Hsupport.
  unfold singleton_closure_matrix in Hrequest, Hsupport. simp_in Hrequest. simp_in Hsupport.
  fassert Hall : (∀ ($0 ∈' c`[↑] → t`[↑] ∈' $0)).
  { fall z. fintro Hzc. pose proof Hsupport as H. finst H z. fmp H Hzc.
    fex H p HP. fcases HP Hroot Hstep.
    - pose proof (CE2 Hroot) as Eza. fmemE.
    - pose proof (CE2 Hstep) as Hpairz. unfold domain_pair in Hpairz. exact (CE1 Hpairz). }
  fassert Hac : (a ∈' c).
  { pose proof Hrequest as H. finst H t.
    fassert Helig : (t ≡' t ∨ ∃ ($0 ∈' c`[↑] ∧ raw_subset t`[↑] $0)).
    { fleft. feqE. }
    unfold raw_subset in Helig. fmp H Helig.
    match type of H with _ ⊢C ?P → _ => fassert Hw : P end.
    { fexists a. fleft. fsplit; feqE. }
    fmp H Hw. fex H z HZ. fdestr HZ Hzc Hcases. fcases Hcases Hroot Hstep.
    - pose proof (CE2 Hroot) as Eza. fmemE.
    - pose proof (CE1 Hstep) as Htt. unfold raw_empty in Hempty. finst Hempty t.
      fabsurd. exact (IE Hempty Htt). }
  fexists c. unfold singleton_closure_profile. fsplit; [fsplit; assumption|].
  fall p. fintro Hpc. pose proof Hall as Htp. finst Htp p. fmp Htp Hpc.
  fobtain (domain_pair_exists _ HB t p p Hpair Hempty Htp Htp) as s HS.
  pose proof Hrequest as H. finst H p.
  fassert Helig : (p ≡' t ∨ ∃ ($0 ∈' c`[↑] ∧ raw_subset p`[↑] $0)).
  { fright. fexists p. fsplit; [exact Hpc|apply raw_subset_refl]. }
  unfold raw_subset in Helig. fmp H Helig.
  match type of H with _ ⊢C ?P → _ => fassert Hw : P end.
  { fexists s. fright. fsplit; assumption. }
  fmp H Hw. fex H z HZ. fdestr HZ Hzc Hcases. fcases Hcases Hroot Hstep.
  - pose proof (CE1 Hroot) as Ept. unfold raw_empty in Hempty. finst Hempty t.
    fabsurd. apply (IE Hempty). fmemE.
  - fexists z. fsplit; [exact Hzc|exact (CE2 Hstep)].
Qed.
