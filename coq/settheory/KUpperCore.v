(** The Separation step in the upper consistency bound.
    Existence of the required bounds remains a separate obligation. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From K230S Require Import KP0 KP0Use KPRaw KPSeed KPrimeCore.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition subset_closed (b : term) : form :=
  ∀ ($0 ∈' b`[↑] → ∀ (raw_subset $0 $1 → $0 ∈' b`[↑]`[↑])).
Definition witness_closed (phi : form) (sg : nat -> term) (b : term) : form :=
  ∀ ($0 ∈' b`[↑] → matrix_request phi (fun k => (sg k)`[↑]) $0 b`[↑]).
Definition trace_predicate (phi : form) : form :=
  ∃ ($0 ∈' $2 ∧ phi[$1 .: $0 .: (fun k => $(3 + k))]).
Definition trace_profile (phi : form) (sg : nat -> term) (b c : term) : form :=
  ∀ ($0 ∈' c`[↑] ↔ ($0 ∈' b`[↑] ∧
    ∃ ($0 ∈' b`[↑]`[↑] ∧ phi[$1 .: $0 .: (fun k => (sg k)`[↑]`[↑])]))).

Lemma trace_predicate_bounded m phi : fb (S (S m)) phi -> fb (S (S m)) (trace_predicate phi).
Proof.
  intros H. unfold trace_predicate. cbn. split; [lia|].
  eapply fb_subst; [exact H|]. intros [|[|k]] Hk; cbn; lia.
Qed.

Lemma trace_exists G m phi sg b :
  fb (S (S m)) phi ->
  In (forall_times (S m) (ax_sep' (trace_predicate phi))) G ->
  G ⊢C ∃ trace_profile phi (fun k => (sg k)`[↑]) b`[↑] $0.
Proof.
  intros Hfb Hsep.
  pose proof (sep_use G (S m) (trace_predicate phi) (b .: sg) b
    Hsep (trace_predicate_bounded m phi Hfb)) as T.
  unfold trace_predicate in T. simp_in T. unfold trace_profile. kconv T.
Qed.

Lemma trace_parent G phi sg b c x :
  G ⊢C trace_profile phi sg b c -> G ⊢C x ∈' c -> G ⊢C x ∈' b.
Proof.
  intros H Hxc. unfold trace_profile in H. finst H x.
  exact (CE1 (iff_l _ _ _ H Hxc)).
Qed.

Lemma trace_member G phi sg b c x p :
  G ⊢C trace_profile phi sg b c -> G ⊢C x ∈' b -> G ⊢C p ∈' b ->
  G ⊢C phi[x .: p .: sg] -> G ⊢C x ∈' c.
Proof.
  intros H Hxb Hpb Hphi. unfold trace_profile in H. finst H x.
  apply (iff_r _ _ _ H). fsplit; [exact Hxb|]. fexists p. fsplit; [exact Hpb|]. kconv Hphi.
Qed.

Lemma trace_request G phi sg b c p :
  G ⊢C witness_closed phi sg b -> G ⊢C trace_profile phi sg b c ->
  G ⊢C p ∈' b -> G ⊢C matrix_request phi sg p c.
Proof.
  intros HW HT Hpb. unfold witness_closed in HW. finst HW p. fmp HW Hpb.
  fassert HR : (matrix_request phi sg p b).
  { unfold matrix_request in HW |- *. kconv HW. }
  clear HW. rename HR into HW.
  unfold matrix_request in HW |- *. fintro Hsome. fmp HW Hsome.
  fex HW x HX. fdestr HX Hxb Hphi. fexists x. fsplit; [|exact Hphi].
  fassert Hphi' : (phi[x .: p .: sg]). { kconv Hphi. }
  exact (trace_member _ phi sg b c x p HT Hxb Hpb Hphi').
Qed.

Lemma trace_emitted_closure G phi sg b c a :
  G ⊢C subset_closed b -> G ⊢C witness_closed phi sg b ->
  G ⊢C trace_profile phi sg b c ->
  G ⊢C (emitted_closure phi)[c .: a .: sg].
Proof.
  intros HS HW HT. unfold emitted_closure. cbn. fall x. fintro Hxc.
  pose proof HT as HX. unfold trace_profile in HX. finst HX x.
  pose proof (iff_l _ _ _ HX Hxc) as HP. fdestr HP Hxb Hsome.
  fex Hsome p HP. fdestr HP Hpb Hphi. fexists p. fsplit; [kconv Hphi|].
  fall u. fintro Hux. fall y. fintro Huy.
  pose proof HS as H. unfold subset_closed in H. finst H x. fmp H Hxb.
  finst H u. fmp H Hux.
  pose proof (trace_request _ phi sg b c u HW HT H) as R.
  unfold matrix_request in R.
  match type of R with _ ⊢C ?P → _ => fassert Hsome : P end.
  { fexists y. kconv Huy. }
  fmp R Hsome. fex R z HZ. fdestr HZ Hzc Hzphi.
  fexists z. fsplit; [|exact Hzc]. kconv Hzphi.
Qed.

Lemma bounded_output_root G m phi sg b a x :
  fb (S (S m)) phi ->
  In (forall_times (S m) (ax_sep' (trace_predicate phi))) G ->
  G ⊢C a ∈' b -> G ⊢C x ∈' b ->
  G ⊢C subset_closed b -> G ⊢C witness_closed phi sg b ->
  G ⊢C ∃ ((phi[x`[↑] .: a`[↑] .: (fun k => (sg k)`[↑])] → x`[↑] ∈' $0) ∧
    (emitted_closure phi)[$0 .: a`[↑] .: (fun k => (sg k)`[↑])]).
Proof.
  intros Hfb Hsep Hab Hxb HS HW.
  fobtain (trace_exists G m phi sg b Hfb Hsep) as c HT.
  fassert HTrace : (trace_profile phi sg b c).
  { unfold trace_profile. kconv HT. }
  fexists c. fsplit.
  - fintro Hphi.
    fassert HP : (phi[x .: a .: sg]). { kconv Hphi. }
    exact (trace_member _ phi sg b c x a HTrace Hxb Hab HP).
  - pose proof (trace_emitted_closure _ phi sg b c a HS HW HTrace) as H.
    unfold emitted_closure in H |- *. simp_in H. cbn. autorewrite with fsub. cbn. kconv H.
Qed.
