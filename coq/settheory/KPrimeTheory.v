(** Ordinary core theories and a constructive translation of finite derivations.
    This does not yet identify either theory with the full machine decoder. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From K230S Require Import KP0 KP0Use KPrimeCore.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Inductive KPrimeOrd : form -> Prop :=
  | KPrimeOrd_eq phi : In phi equality_axioms -> KPrimeOrd phi
  | KPrimeOrd_instance phi n : closedf (forall_times n (kprime_core phi)) ->
      KPrimeOrd (forall_times n (kprime_core phi)).

Definition KPrimeOrdIR phi : Prop := KPrimeOrd phi \/ phi = irreflexivity.

Lemma KPrimeOrd_closed phi : KPrimeOrd phi -> closedf phi.
Proof.
  intros [psi H | psi n H]; [|exact H].
  repeat (destruct H as [<-|H]; [cbn; lia|]). destruct H.
Qed.

Lemma forall_times_intro_closed G (HG : forall a, In a G -> closedf a) :
  forall n phi, G ⊢C phi -> G ⊢C forall_times n phi.
Proof.
  induction n as [|n IH]; intros phi H; [exact H|].
  change (G ⊢C ∀ (forall_times n phi)).
  apply AllI_closed; [exact HG|]. apply IH, H.
Qed.

Lemma KPrimeOrd_proves_kp0 n phi : KPrimeOrd ⊢TC forall_times n (kp0 phi).
Proof.
  destruct (fb_exists phi) as [m Hm].
  assert (Hfb : fb (S (S m)) phi) by (eapply fb_mono; [exact Hm|lia]).
  assert (Hclosed : closedf (forall_times m (kprime_core phi))) by
    (apply kprime_core_closed, Hfb).
  set (B := EqAx ++ [forall_times m (kprime_core phi)]).
  assert (HE : incl EqAx B) by (intros b Hb; apply in_or_app; now left).
  assert (HB : forall b, In b B -> KPrimeOrd b).
  { intros b Hb. apply in_app_or in Hb as [Hb|[<-|[]]].
    - apply KPrimeOrd_eq. exact Hb.
    - apply KPrimeOrd_instance. exact Hclosed. }
  assert (HC : forall b, In b B -> closedf b) by
    (intros b Hb; apply KPrimeOrd_closed, HB, Hb).
  exists B. split; [exact HB|].
  assert (H : B ⊢C forall_times m (kprime_core phi)) by
    (apply Ctx, in_or_app; right; now left).
  apply (closed_inst _ _ _ var Hclosed) in H. rewrite subst_var in H.
  apply forall_times_intro_closed; [exact HC|].
  exact (kprime_core_to_kp0 _ HE phi H).
Qed.

(** Only finitely many proof witnesses are collected. No choice principle is used. *)
Lemma collect_theory_proofs (U : form -> Prop) (A : list form) :
  (forall a, In a A -> U ⊢TC a) ->
  exists B, (forall b, In b B -> U b) /\ (forall a, In a A -> B ⊢C a).
Proof.
  induction A as [|a A IH]; intros H.
  - exists []. split; intros b Hb; contradiction.
  - destruct (H a (or_introl eq_refl)) as [B [HB Ha]].
    destruct (IH ltac:(intros b Hb; apply H; now right)) as [C [HC HA]].
    exists (B ++ C). split.
    + intros b Hb. apply in_app_or in Hb as [Hb|Hb]; [apply HB|apply HC]; assumption.
    + intros b [<-|Hb].
      * eapply Weak; [exact Ha|]. intros c Hc. apply in_or_app. now left.
      * eapply Weak; [apply HA, Hb|]. intros c Hc. apply in_or_app. now right.
Qed.

Theorem theory_derivation_map (T U : form -> Prop) phi :
  (forall a, T a -> U ⊢TC a) -> T ⊢TC phi -> U ⊢TC phi.
Proof.
  intros HT [A [HA H]].
  destruct (collect_theory_proofs U A ltac:(intros a Ha; apply HT, HA, Ha)) as [B [HB HBA]].
  exists B. split; [exact HB|]. exact (prv_cut H HBA).
Qed.

Theorem K0_derivation_to_KPrimeOrd phi : K0 ⊢TC phi -> KPrimeOrd ⊢TC phi.
Proof.
  apply theory_derivation_map. intros a Ha. destruct Ha as [a Ha|p n Hp].
  - exists [a]. split.
    + intros b [<-|[]]. now apply KPrimeOrd_eq.
    + apply Ctx. now left.
  - apply KPrimeOrd_proves_kp0.
Qed.
