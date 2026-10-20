(** * S_gic: using GIC closures; raw separation in S0

    [gic_use]: instantiate a closed GIC closure at parameters [sg] and domain [B].
    [sep_th psi]: the GIC matrix θ(u,v; A, p) := (u ∈ A ∧ v ≡ u) ∧ psi(v; p), whose collection over
    the domain A is the raw separation {v ∈ A | psi(v)}.  [sepS_use] proves it from the closure
    of [gic (sep_th psi)] and the atomic congruence axiom only. *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From OldM254S Require Import S_def.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.
#[local] Set Default Proof Using "All".

(** convert a fact to the goal when both are substitution instances of one formula *)
Ltac feq_form := repeat (first [reflexivity | form_subst_eq | progress f_equal]).
Ltac fconv_h H :=
  match type of H with _ ⊢C ?f => match goal with |- _ ⊢C ?g =>
    replace g with f by feq_form; exact H end end.
(** modus ponens up to substitution normalization of the antecedent *)
Ltac fmp_conv H H' :=
  match type of H with ?G ⊢C ?A → _ =>
    let T := fresh in assert (T : G ⊢C A) by fconv_h H'; fmp H T; clear T end.

Lemma gic_closed n (phi : form) : fb (S (S n)) phi -> closedf (forall_times n (gic phi)).
Proof.
  intros H. unfold closedf. apply fb_forall_times_inv. rewrite Nat.add_0_r. cbn.
  repeat split; try lia; (eapply fb_subst; [exact H|]); intros [|[|i]] Hi; cbn; lia.
Qed.

Lemma gic_use G n (phi : form) (sg : nat -> term) B :
  In (forall_times n (gic phi)) G -> fb (S (S n)) phi ->
  G ⊢C ∃ ((∀ ($0 ∈' B`[↑]`[↑] → ∀ (phi[$1 .: $0 .: (fun k => (sg k)`[↑]`[↑]`[↑])] →
              ∃ (phi[$2 .: $0 .: (fun k => (sg k)`[↑]`[↑]`[↑]`[↑])] ∧ $0 ∈' $3))))
         ∧ ∀ ($0 ∈' $1 → ∃ phi[$0 .: $1 .: (fun k => (sg k)`[↑]`[↑]`[↑])])).
Proof.
  intros Hin Hfb. assert (H : G ⊢C forall_times n (gic phi)) by now apply Ctx.
  apply (closed_inst _ _ _ sg (gic_closed _ _ Hfb)) in H. apply (AllE B) in H. cbn in H.
  replace (phi[$1 .: $0 .: (fun k => (sg k)`[↑]`[↑]`[↑])])
    with (phi[$1 .: $0 .: (fun k => $(4 + k))][up (up (up (up sg)))][up (up (up B..))])
    by form_subst_eq.
  replace (phi[$2 .: $0 .: (fun k => (sg k)`[↑]`[↑]`[↑]`[↑])])
    with (phi[$2 .: $0 .: (fun k => $(5 + k))][up (up (up (up (up sg))))][up (up (up (up B..)))])
    by form_subst_eq.
  replace (phi[$0 .: $1 .: (fun k => (sg k)`[↑]`[↑]`[↑])])
    with (phi[$0 .: $1 .: (fun k => $(4 + k))][up (up (up (up sg)))][up (up (up B..))])
    by form_subst_eq.
  exact H.
Qed.

(** ** Raw separation *)
Definition sep_th (psi : form) : form := ($0 ∈' $2 ∧ $1 ≡' $0) ∧ psi[$1 .: (fun k => $(3 + k))].

Lemma fb_sep_th n psi : fb (S n) psi -> fb (S (S (S n))) (sep_th psi).
Proof.
  intros H. unfold sep_th. cbn. repeat split; try lia.
  eapply fb_subst; [exact H|]. intros [|i] Hi; cbn; lia.
Qed.

Lemma sepS_use G n (psi : form) (sg : nat -> term) a :
  incl EqAx G -> In (forall_times (S n) (gic (sep_th psi))) G -> fb (S n) psi ->
  G ⊢C ∃ ∀ ($0 ∈' $1 ↔ $0 ∈' a`[↑]`[↑] ∧ psi[$0 .: (fun k => (sg k)`[↑]`[↑])]).
Proof.
  intros HE Hin Hfb.
  pose proof (gic_use G (S n) (sep_th psi) (a .: sg) a Hin (fb_sep_th n psi Hfb)) as T.
  fex T C HC. fdestr HC Hcov Hnx. fexists C. fall z. fsplit.
  - fintro Hz. finst Hnx z. fmp Hnx Hz. fex Hnx u Hu. unfold sep_th in Hu. simp_in Hu.
    fdestr Hu Hu12 Hp. fdestr Hu12 Hu1 Hu2. fsplit.
    + exact (elemE_cong HE u a z a (eqE_sym HE _ _ Hu2) (eqE_refl HE a) Hu1).
    + fconv_h Hp.
  - fintro Hz. fdestr Hz Hza Hp. finst Hcov z. fmp Hcov Hza. finst Hcov z.
    unfold sep_th in Hcov. simp_in Hcov.
    fassert Hth : ((z ∈' a ∧ z ≡' z) ∧ psi[$1 .: (fun k => $(3 + k))][z .: z .: (fun k => (a .: sg) k)]).
    { fsplit; [fsplit; [exact Hza | apply eqE_refl; exact HE] | fconv_h Hp]. }
    fmp_conv Hcov Hth. fex Hcov v Hv. fdestr Hv Hv1 Hv2. fdestr Hv1 Hv11 Hv12. fdestr Hv11 Hv111 Hv112.
    exact (elemE_cong HE v C z C Hv112 (eqE_refl HE C) Hv2).
Qed.
