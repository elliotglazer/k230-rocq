(** The ordinary K230 output-root core, after assigning distinct variable roles.
    Full numerical decoding and exceptional low-code cases are separate. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From K230S Require Import KP0 KP0Use KPSeed KPRaw.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

(** Free roles: container 0, seed input 1, remaining matrix parameters 2+k.
    The support witness's input is shadowed by the following universal input.
    Conjunction order agrees with the promoted 230-state source. *)
Definition emitted_closure (phi : form) : form :=
  ∀ ($0 ∈' $1 → ∃
     (phi[$1 .: $0 .: (fun k => $(4 + k))] ∧
      ∀ (raw_subset $0 $2 →
         ∀ (phi[$0 .: $1 .: (fun k => $(6 + k))] →
            ∃ (phi[$0 .: $2 .: (fun k => $(7 + k))] ∧ $0 ∈' $5))))).

Definition kprime_core (phi : form) : form := ∀ output_root phi (emitted_closure phi).
Definition seeded_core (phi : form) : form := ∀ seed_root phi (emitted_closure phi).

Lemma kprime_core_closed n phi : fb (S (S n)) phi ->
  closedf (forall_times n (kprime_core phi)).
Proof.
  intros H. unfold closedf. apply fb_forall_times_inv. rewrite Nat.add_0_r.
  unfold kprime_core, output_root, emitted_closure, raw_subset. cbn.
  repeat rewrite subst_comp. cbn.
  repeat split; try lia; (eapply fb_subst; [exact H|]);
    intros [|[|k]] Hk; cbn; lia.
Qed.

Lemma output_root_subst P H sg :
  (output_root P H)[sg] = output_root (P[up sg]) (H[up sg]).
Proof. unfold output_root. cbn. kform_eq. Qed.

Lemma seed_root_subst P H sg :
  (seed_root P H)[sg] = seed_root (P[up sg]) (H[up sg]).
Proof. unfold seed_root. cbn. kform_eq. Qed.

Theorem kprime_core_to_seed G phi : G ⊢C kprime_core phi -> G ⊢C seeded_core phi.
Proof.
  unfold kprime_core, seeded_core. intros H.
  apply AllI_named. intros a. apply (AllE a) in H.
  rewrite output_root_subst in H. rewrite seed_root_subst.
  exact (output_root_to_seed _ _ _ H).
Qed.

Definition matrix_request (phi : form) (rho : nat -> term) (p c : term) : form :=
  (∃ phi[$0 .: p`[↑] .: (fun k => (rho k)`[↑])]) →
  ∃ ($0 ∈' c`[↑] ∧ phi[$0 .: p`[↑] .: (fun k => (rho k)`[↑])]).

Lemma matrix_request_congr G (HE : incl EqAx G) phi rho p q c :
  G ⊢C p ≡' q -> G ⊢C matrix_request phi rho p c -> G ⊢C matrix_request phi rho q c.
Proof.
  intros E H.
  set (F := matrix_request phi (fun k => (rho k)`[↑]) $0 c`[↑]).
  assert (Hp : G ⊢C F[p..]).
  { unfold F, matrix_request in *. cbn. autorewrite with fsub. cbn. kconv H. }
  pose proof (leibE G F p q HE E Hp) as Hq.
  unfold F, matrix_request in *. cbn in Hq. autorewrite with fsub in Hq. cbn in Hq. kconv Hq.
Qed.

Theorem seeded_core_to_kp0 G (HE : incl EqAx G) phi :
  G ⊢C seeded_core phi -> G ⊢C kp0 phi.
Proof.
  intros Hsource. unfold kp0. fall a.
  unfold seeded_core in Hsource. finst Hsource a.
  unfold seed_root in Hsource. simp_in Hsource.
  fex Hsource C HC. fdestr HC Hseed Hclosure.
  fexists C. fsplit.
  - fall p. fintro Helig. fcases Helig Hpa Hrecursive.
    + fassert Hseed' : (matrix_request phi var a C).
      { unfold matrix_request. kconv Hseed. }
      pose proof (matrix_request_congr _ HE phi var a p C (eqE_sym HE _ _ Hpa) Hseed') as T.
      unfold matrix_request in T. kconv T.
    + fex Hrecursive u Hu. fdestr Hu HuC Hpu.
      pose proof Hclosure as H. unfold emitted_closure in H. simp_in H.
      finst H u. fmp H HuC. fex H oldInput Hbody.
      pose proof (CE2 Hbody) as Hrequests. finst Hrequests p.
      match type of Hrequests with _ ⊢C ?A → _ => fassert Hsub : A end.
      { kconv Hpu. }
      fmp Hrequests Hsub.
      fintro Hex. fex Hex x Hx. finst Hrequests x.
      match type of Hrequests with _ ⊢C ?A → _ => fassert Hmatrix : A end.
      { kconv Hx. }
      fmp Hrequests Hmatrix. fex Hrequests y Hy.
      fexists y. fsplit.
      * exact (CE2 Hy).
      * pose proof (CE1 Hy) as Hphi. kconv Hphi.
  - fall x. fintro HxC.
    unfold emitted_closure in Hclosure. simp_in Hclosure.
    finst Hclosure x. fmp Hclosure HxC. fex Hclosure p Hp.
    fexists p. pose proof (CE1 Hp) as Hphi. kconv Hphi.
Qed.

Theorem kprime_core_to_kp0 G (HE : incl EqAx G) phi :
  G ⊢C kprime_core phi -> G ⊢C kp0 phi.
Proof. intros H. apply (seeded_core_to_kp0 _ HE), kprime_core_to_seed, H. Qed.
