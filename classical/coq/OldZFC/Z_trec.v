(** * Z_trec: transfinite recursion along the ordinals for a step formula [S].

    [S] has $0 = f (the function built so far, read only below ξ), $1 = ξ, $2 = v (the value
    at ξ), $3 = p (a parameter); [SR S f ξ v p] instantiates it (all other variables ↦ p).
    [RecOK S p f]: every pair (ξ, v) ∈ f satisfies S(f, ξ, v, p). *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_setinf.
From OldZFC Require Import Z_rel Z_base Z_prim Z_ord.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.
#[local] Set Default Proof Using "All".

Definition SR (S : form) (f xi v p : term) : form := S[f .: xi .: v .: p .: (fun _ => p)].
#[global] Arguments SR : simpl never.
Lemma SR_subst S f xi v p sg : (SR S f xi v p)[sg] = SR S f`[sg] xi`[sg] v`[sg] p`[sg].
Proof. unfold SR. rewrite subst_comp. apply subst_ext. intros [|[|[|[|n]]]]; reflexivity. Qed.
#[global] Hint Rewrite SR_subst : fsub.

Definition RecOK (S : form) (p f : term) : form := PairsAll f (SR S f`[↑]`[↑] $1 $0 p`[↑]`[↑]).
#[global] Arguments RecOK : simpl never.
Lemma RecOK_subst S p f sg : (RecOK S p f)[sg] = RecOK S p`[sg] f`[sg].
Proof. unfold RecOK. rewrite PairsAll_subst. f_equal. simp. reflexivity. Qed.
#[global] Hint Rewrite RecOK_subst : fsub.

(** f and f' agree below ξ *)
Definition Agree (f f' xi : term) : form :=
  ∀ ($0 ∈' xi`[↑] → ∀ (App0 f`[↑]`[↑] $1 $0 ↔ App0 f'`[↑]`[↑] $1 $0)).
#[global] Arguments Agree : simpl never.
Lemma Agree_subst f f' xi sg : (Agree f f' xi)[sg] = Agree f`[sg] f'`[sg] xi`[sg].
Proof. psubst Agree. Qed.
#[global] Hint Rewrite Agree_subst : fsub.

(** the three hypotheses on the step formula, for a fixed parameter p: locality (S(f,ξ,v)
    depends only on f below ξ), totality (given values below ξ), functionality *)
Definition SLoc (S : form) (p : term) : form :=
  ∀ (∀ (∀ (∀ (Fun0 $3 → Fun0 $2 → Ord0 $1 → Agree $3 $2 $1 →
       SR S $3 $1 $0 p`[↑]`[↑]`[↑]`[↑] → SR S $2 $1 $0 p`[↑]`[↑]`[↑]`[↑])))).
Definition STot (S : form) (p : term) : form :=
  ∀ (∀ (Fun0 $1 → Ord0 $0 → (∀ ($0 ∈' $1 → ∃ App0 $3 $1 $0)) → ∃ SR S $2 $1 $0 p`[↑]`[↑]`[↑])).
Definition SFun (S : form) (p : term) : form :=
  ∀ (∀ (∀ (∀ (Fun0 $3 → Ord0 $2 → SR S $3 $2 $1 p`[↑]`[↑]`[↑]`[↑] → SR S $3 $2 $0 p`[↑]`[↑]`[↑]`[↑] → $1 ≡' $0)))).

(** ** Helper predicates of the construction *)
(** f and f' agree at x (single values) *)
Definition AgF (f f' x : term) : form :=
  ∀ (∀ (App0 f`[↑]`[↑] x`[↑]`[↑] $1 → App0 f'`[↑]`[↑] x`[↑]`[↑] $0 → $1 ≡' $0)).
(** some recursion function with domain d *)
Definition RecFn (S : form) (p d : term) : form := ∃ (Fun0 $0 ∧ Dom0 $0 d`[↑] ∧ RecOK S p`[↑] $0).
(** v is the S-value at the ordinal a, computed from a recursion function g on an ordinal e ⊇ a *)
Definition Ok (S : form) (p a v : term) : form :=
  Ord0 a ∧ ∃ (∃ (Ord0 $1 ∧ Sub0 a`[↑]`[↑] $1 ∧ Fun0 $0 ∧ Dom0 $0 $1 ∧ RecOK S p`[↑]`[↑] $0 ∧
                 SR S $0 a`[↑]`[↑] v`[↑]`[↑] p`[↑]`[↑])).
(** q = (a, v) with Ok S p a v *)
Definition Gr (S : form) (p a q : term) : form := ∃ (OP0 a`[↑] $0 q`[↑] ∧ Ok S p`[↑] a`[↑] $0).
#[global] Arguments AgF : simpl never.
#[global] Arguments RecFn : simpl never.
#[global] Arguments Ok : simpl never.
#[global] Arguments Gr : simpl never.

Lemma AgF_subst f f' x sg : (AgF f f' x)[sg] = AgF f`[sg] f'`[sg] x`[sg].
Proof. psubst AgF. Qed.
Lemma RecFn_subst S p d sg : (RecFn S p d)[sg] = RecFn S p`[sg] d`[sg].
Proof. psubst RecFn. Qed.
Lemma Ok_subst S p a v sg : (Ok S p a v)[sg] = Ok S p`[sg] a`[sg] v`[sg].
Proof. psubst Ok. Qed.
#[global] Hint Rewrite AgF_subst RecFn_subst Ok_subst : fsub.
Lemma Gr_subst S p a q sg : (Gr S p a q)[sg] = Gr S p`[sg] a`[sg] q`[sg].
Proof. psubst Gr. Qed.
#[global] Hint Rewrite Gr_subst : fsub.

(** the schema formulas: induction for agreement ($0 = ξ, $1 = f, $2 = f'), induction for existence
    ($0 = d, $1 = p), replacement for the graph ($0 = ξ, $1 = the pair, $2 = p) *)
Definition psiA : form := AgF $1 $2 $0.
Definition psiE (S : form) : form := RecFn S $1 $0.
Definition phiR (S : form) : form := Gr S $2 $0 $1.

Lemma fb_SR S f xi v p N : idx f < N -> idx xi < N -> idx v < N -> idx p < N -> fb N (SR S f xi v p).
Proof.
  intros H1 H2 H3 H4. destruct (fb_exists S) as [M HM]. unfold SR. eapply fb_subst; [exact HM|].
  intros [|[|[|[|i]]]] _; cbn; assumption.
Qed.

Ltac fbsolve :=
  unfold psiA, psiE, phiR, AgF, RecFn, Gr, Ok, RecOK, Fun0, Dom0, Ord0, Sub0, Trans0, IsRel0, PairsAll,
    App0, OP0, Sing0, Pair0;
  repeat (first [ exact I | progress cbn | split | lia | progress rewrite ?SR_subst
                | (apply fb_SR; cbn; lia) ]).

Lemma fb_psiA : fb 3 psiA.
Proof. fbcomp. Qed.
Lemma fb_psiE S : fb 2 (psiE S).
Proof. fbsolve. Qed.
Lemma fb_phiR S : fb 3 (phiR S).
Proof. fbsolve. Qed.

(** instances used by the recursion theorem for the step formula S *)
Definition rec_insts (S : form) : list form :=
  [least_inst 2 (¬ psiA); least_inst 1 (¬ psiE S); forall_times 1 (ax_rep' (phiR S))].
Lemma rec_insts_ok S a : fb 4 S -> In a (rec_insts S) -> ZFR a.
Proof.
  intros _ [<-|[<-|[<-|[]]]]; unfold least_inst.
  - apply ZFR_sep. split; [exact fb_psiA|exact I].
  - apply ZFR_sep. split; [exact (fb_psiE S)|exact I].
  - apply ZFR_rep. exact (fb_phiR S).
Qed.

Lemma in_insA {G} S : incl (rec_insts S) G -> In (least_inst 2 (¬ psiA)) G.
Proof. intros H. apply H. now left. Qed.
Lemma in_insE {G} S : incl (rec_insts S) G -> In (least_inst 1 (¬ psiE S)) G.
Proof. intros H. apply H. right. now left. Qed.
Lemma in_insR {G} S : incl (rec_insts S) G -> In (forall_times 1 (ax_rep' (phiR S))) G.
Proof. intros H. apply H. right. right. now left. Qed.

Lemma incl_t {X} {l m n : list X} : incl l m -> incl m n -> incl l n.
Proof. intros H1 H2 a Ha. apply H2, H1, Ha. Qed.

(** ** Wrappers for upstream lemmas (robust against changes of their section arguments) *)
Section W.
Context {G : list form} (HG : incl ZF0base G) (HP : incl Ax_prim G).
Lemma w_pairsall_use f B u v : G ⊢C PairsAll f B -> G ⊢C App0 f u v -> G ⊢C B[v .: u .: var].
Proof. intros. eapply pairsall_use; eassumption. Qed.
Lemma w_pairsall_intro f B :
  (forall G' u v, incl G G' -> G' ⊢C App0 f u v -> G' ⊢C B[v .: u .: var]) -> G ⊢C PairsAll f B.
Proof. intros. eapply pairsall_intro; eassumption. Qed.
(** (Z_prim.op0_comp is stated without parentheses around the first ∃, so its second
    existential is mis-scoped; this is the intended statement, proved from the definition.) *)
Lemma w_op0_comp x y p : G ⊢C OP0 x y p ->
  G ⊢C (∃ ($0 ∈' p`[↑] ∧ x`[↑] ∈' $0)) ∧ ∃ ($0 ∈' p`[↑] ∧ y`[↑] ∈' $0).
Proof.
  intros H. unfold OP0 in H. fdestr H H12 H3. fdestr H12 H1 H2. fsplit.
  - fex H1 s Hs. fdestr Hs Hs1 Hs2. fexists s. fsplit; [exact Hs1|]. unfold Sing0 in Hs2. exact (CE1 Hs2).
  - fex H2 t Ht. fdestr Ht Ht1 Ht2. fexists t. fsplit; [exact Ht1|]. unfold Pair0 in Ht2. exact (CE2 (CE1 Ht2)).
Qed.
Lemma w_op0_ex x y : G ⊢C ∃ OP0 x`[↑] y`[↑] $0.
Proof. intros. eapply op0_ex; eassumption. Qed.
Lemma w_op0_unique x y p p' : G ⊢C OP0 x y p -> G ⊢C OP0 x y p' -> G ⊢C p ≡' p'.
Proof. intros. eapply op0_unique; eassumption. Qed.
Lemma w_op0_inj x y x' y' p : G ⊢C OP0 x y p -> G ⊢C OP0 x' y' p -> G ⊢C x ≡' x' ∧ y ≡' y'.
Proof. intros. eapply op0_inj; eassumption. Qed.
Lemma w_app0_intro f u v p : G ⊢C OP0 u v p -> G ⊢C p ∈' f -> G ⊢C App0 f u v.
Proof. intros. eapply app0_intro; eassumption. Qed.
Lemma w_dom0_app f d u : G ⊢C Dom0 f d -> G ⊢C u ∈' d -> G ⊢C ∃ App0 f`[↑] u`[↑] $0.
Proof. intros. eapply dom0_app; eassumption. Qed.
Lemma w_dom0_in f d u v : G ⊢C Dom0 f d -> G ⊢C App0 f u v -> G ⊢C u ∈' d.
Proof. intros. eapply dom0_in; eassumption. Qed.
End W.
Section WO.
Context {G : list form} (HG : incl ZF0base G) (HR : In ax_reg' G) (HO : incl Ax_ord G).
Lemma w_ord_el a x : G ⊢C Ord0 a -> G ⊢C x ∈' a -> G ⊢C Ord0 x.
Proof. intros. eapply ord_el; eassumption. Qed.
Lemma w_ord_tr a x y : G ⊢C Ord0 a -> G ⊢C x ∈' y -> G ⊢C y ∈' a -> G ⊢C x ∈' a.
Proof. intros. eapply ord_tr; eassumption. Qed.
Lemma w_ord_el_sub a b : G ⊢C Ord0 b -> G ⊢C a ∈' b -> G ⊢C Sub0 a b.
Proof. intros. eapply ord_el_sub; eassumption. Qed.
Lemma w_ord_ind n psi sg a : fb (S n) psi -> In (least_inst n (¬ psi)) G ->
  G ⊢C ∀ (Ord0 $0 → (∀ ($0 ∈' $1 → psi[up (sg >> subst_term ↑)])) → psi[up sg]) ->
  G ⊢C Ord0 a -> G ⊢C psi[a .: sg].
Proof. intros. eapply ord_ind; eassumption. Qed.
End WO.

(** ** Accessors and introduction rules (any context) *)
Section Acc.
Context {G : list form} (HG : incl ZF0base G) (HP : incl Ax_prim G).

Lemma sub_use x y z : G ⊢C Sub0 x y -> G ⊢C z ∈' x -> G ⊢C z ∈' y.
Proof. intros H Hz. unfold Sub0 in H. finst H z. fmp H Hz. exact H. Qed.

Lemma sub_refl0 x : G ⊢C Sub0 x x.
Proof. unfold Sub0. fall z. fintro Hz. exact Hz. Qed.

Lemma recok_use S p f u v : G ⊢C RecOK S p f -> G ⊢C App0 f u v -> G ⊢C SR S f u v p.
Proof.
  intros H1 H2. unfold RecOK in H1. pose proof (w_pairsall_use HG HP _ _ u v H1 H2) as H. simp_in H. exact H.
Qed.

Lemma sloc_use S p f f' x v : G ⊢C SLoc S p -> G ⊢C Fun0 f -> G ⊢C Fun0 f' -> G ⊢C Ord0 x ->
  G ⊢C Agree f f' x -> G ⊢C SR S f x v p -> G ⊢C SR S f' x v p.
Proof.
  intros H H1 H2 H3 H4 H5. unfold SLoc in H. finst H f f' x v.
  fmp H H1. fmp H H2. fmp H H3. fmp H H4. fmp H H5. exact H.
Qed.

Lemma stot_use S p f x : G ⊢C STot S p -> G ⊢C Fun0 f -> G ⊢C Ord0 x ->
  G ⊢C ∀ ($0 ∈' x`[↑] → ∃ App0 f`[↑]`[↑] $1 $0) -> G ⊢C ∃ SR S f`[↑] x`[↑] $0 p`[↑].
Proof.
  intros H H1 H2 H3. unfold STot in H. finst H f x. fmp H H1. fmp H H2. fmp H H3. exact H.
Qed.

Lemma sfun_use S p f x v v' : G ⊢C SFun S p -> G ⊢C Fun0 f -> G ⊢C Ord0 x ->
  G ⊢C SR S f x v p -> G ⊢C SR S f x v' p -> G ⊢C v ≡' v'.
Proof.
  intros H H1 H2 H3 H4. unfold SFun in H. finst H f x v v'. fmp H H1. fmp H H2. fmp H H3. fmp H H4. exact H.
Qed.

Lemma isrel0_intro f : G ⊢C ∀ ($0 ∈' f`[↑] → ∃ (∃ (OP0 $1 $0 $2))) -> G ⊢C IsRel0 f.
Proof.
  intros H. unfold IsRel0. fall q. fintro Hq. finst H q. fmp H Hq. fex H a Ha. fex Ha v Hv.
  fhave C : (w_op0_comp HG HP a v q Hv). fdestr C C1 C2. fex C1 s Hs. fdestr Hs Hs1 Hs2.
  fex C2 s' Hs'. fdestr Hs' Hs'1 Hs'2.
  fexists s. fsplit; [exact Hs1|]. fexists a. fsplit; [exact Hs2|].
  fexists s'. fsplit; [exact Hs'1|]. fexists v. fsplit; [exact Hs'2|exact Hv].
Qed.

Lemma fun0_intro f : G ⊢C IsRel0 f ->
  G ⊢C ∀ (∀ (∀ (App0 f`[↑]`[↑]`[↑] $2 $1 → App0 f`[↑]`[↑]`[↑] $2 $0 → $1 ≡' $0))) -> G ⊢C Fun0 f.
Proof.
  intros Hr Hf. unfold Fun0. fsplit; [exact Hr|].
  apply (w_pairsall_intro HG HP). intros G1 u v H1 Huv. simp.
  apply (w_pairsall_intro (incl_t HG H1) (incl_t HP H1)). intros G2 u' v' H2 Huv'. simp.
  assert (Hf2 : G2 ⊢C ∀ (∀ (∀ (App0 f`[↑]`[↑]`[↑] $2 $1 → App0 f`[↑]`[↑]`[↑] $2 $0 → $1 ≡' $0))))
    by (eapply Weak; [exact Hf|exact (incl_t H1 H2)]).
  assert (Huv2 : G2 ⊢C App0 f u v) by (eapply Weak; [exact Huv|exact H2]).
  pose proof (incl_t (incl_t HG H1) H2) as HG2.
  clear Hf Huv. fintro E. finst Hf2 u' v v'.
  frew_in E (App0 f`[↑] $0 v`[↑]) Huv2.
  fmp Hf2 Huv2. fmp Hf2 Huv'. exact Hf2.
Qed.

Lemma dom0_intro f d : G ⊢C ∀ ($0 ∈' d`[↑] → ∃ App0 f`[↑]`[↑] $1 $0) ->
  G ⊢C ∀ (∀ (App0 f`[↑]`[↑] $1 $0 → $1 ∈' d`[↑]`[↑])) -> G ⊢C Dom0 f d.
Proof.
  intros H1 H2. unfold Dom0. fsplit.
  - fall a. fintro Ha. finst H1 a. fmp H1 Ha. fex H1 v Hv. pose proof Hv as Hv'. unfold App0 in Hv'.
    fex Hv' q Hq. fdestr Hq Hq1 Hq2. fhave C : (w_op0_comp HG HP a v q Hq2). fdestr C C1 C2.
    fex C2 s Hs. fdestr Hs Hs1 Hs2.
    fexists q. fsplit; [exact Hq1|]. fexists s. fsplit; [exact Hs1|]. fexists v. fsplit; [exact Hs2|exact Hq2].
  - apply (w_pairsall_intro HG HP). intros G1 u v Hi Huv. simp.
    assert (H2' : G1 ⊢C ∀ (∀ (App0 f`[↑]`[↑] $1 $0 → $1 ∈' d`[↑]`[↑]))) by (eapply Weak; [exact H2|exact Hi]).
    finst H2' u v. fmp H2' Huv. exact H2'.
Qed.

Lemma recok_intro S p f : G ⊢C ∀ (∀ (App0 f`[↑]`[↑] $1 $0 → SR S f`[↑]`[↑] $1 $0 p`[↑]`[↑])) -> G ⊢C RecOK S p f.
Proof.
  intros H. unfold RecOK. apply (w_pairsall_intro HG HP). intros G1 u v Hi Huv. simp.
  assert (H' : G1 ⊢C ∀ (∀ (App0 f`[↑]`[↑] $1 $0 → SR S f`[↑]`[↑] $1 $0 p`[↑]`[↑]))) by (eapply Weak; [exact H|exact Hi]).
  finst H' u v. fmp H' Huv. exact H'.
Qed.

End Acc.

Ltac okd H Ha e g Hoe Hsub Hfun Hdom Hrec Hsr :=
  unfold Ok in H;
  let A := fresh "A" in let B := fresh "B" in let C := fresh "C" in
  fdestr H Ha A; fex A e B; fex B g C;
  let T5 := fresh "T" in fdestr C T5 Hsr;
  let T4 := fresh "T" in fdestr T5 T4 Hrec;
  let T3 := fresh "T" in fdestr T4 T3 Hdom;
  let T2 := fresh "T" in fdestr T3 T2 Hfun;
  fdestr T2 Hoe Hsub.

Lemma ok_intro {G} (HG : incl ZF0base G) S p a v e g : G ⊢C Ord0 a -> G ⊢C Ord0 e -> G ⊢C Sub0 a e ->
  G ⊢C Fun0 g -> G ⊢C Dom0 g e -> G ⊢C RecOK S p g -> G ⊢C SR S g a v p -> G ⊢C Ok S p a v.
Proof.
  intros H1 H2 H3 H4 H5 H6 H7. unfold Ok. fsplit; [exact H1|]. fexists e. fexists g.
  fsplit; [|exact H7]. fsplit; [|exact H6]. fsplit; [|exact H5]. fsplit; [|exact H4]. fsplit; [exact H2|exact H3].
Qed.

(** ** Agreement by transfinite induction *)
Lemma agf_ind {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HO : incl Ax_ord G) S
  (HI : incl (rec_insts S) G) p d d' f f' :
  G ⊢C SLoc S p -> G ⊢C SFun S p ->
  G ⊢C Ord0 d -> G ⊢C Fun0 f -> G ⊢C Dom0 f d -> G ⊢C RecOK S p f ->
  G ⊢C Ord0 d' -> G ⊢C Fun0 f' -> G ⊢C Dom0 f' d' -> G ⊢C RecOK S p f' ->
  forall x, G ⊢C Ord0 x -> G ⊢C AgF f f' x.
Proof.
  intros Hsl Hsf Hd Hf Hfd Hfr Hd' Hf' Hfd' Hfr' x Hx.
  pose proof (Ax_ord_prim _ HO) as HP.
  pose proof (w_ord_ind HG HR HO 2 psiA (f .: f' .: var) x fb_psiA (in_insA S HI)) as Hind.
  unfold psiA in Hind. simp_in Hind. apply Hind; [|exact Hx]. clear Hind.
  fall y. fintro Hy. fintro IH. unfold AgF. fall u. fall u'. fintro Hu. fintro Hu'.
  fhave Hyd : (w_dom0_in HG HP f d y u Hfd Hu). fhave Hyd' : (w_dom0_in HG HP f' d' y u' Hfd' Hu').
  fhave H1 : (recok_use HG HP S p f y u Hfr Hu).
  fassert Hag : (Agree f f' y).
  { unfold Agree. fall z. fintro Hz. fall w. fsplit.
    - fintro Hw. fhave Hzd' : (w_ord_tr HG HR HO d' z y Hd' Hz Hyd').
      fobtain (w_dom0_app HG HP f' d' z Hfd' Hzd') as w' Hw'.
      pose proof IH as IHz. finst IHz z. fmp IHz Hz. unfold AgF in IHz. finst IHz w w'.
      fmp IHz Hw. fmp IHz Hw'. frew IHz (App0 f'`[↑] z`[↑] $0). exact Hw'.
    - fintro Hw. fhave Hzd : (w_ord_tr HG HR HO d z y Hd Hz Hyd).
      fobtain (w_dom0_app HG HP f d z Hfd Hzd) as w' Hw'.
      pose proof IH as IHz. finst IHz z. fmp IHz Hz. unfold AgF in IHz. finst IHz w' w.
      fmp IHz Hw'. fmp IHz Hw. frew IHz (App0 f`[↑] z`[↑] $0). exact Hw'. }
  fhave H2 : (sloc_use HG HP S p f f' y u Hsl Hf Hf' Hy Hag H1).
  fhave H3 : (recok_use HG HP S p f' y u' Hfr' Hu').
  exact (sfun_use HG HP S p f' y u u' Hsf Hf' Hy H2 H3).
Qed.

Lemma rec_agree0 {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HO : incl Ax_ord G) S
  (HI : incl (rec_insts S) G) p d d' f f' xi u u' :
  G ⊢C SLoc S p -> G ⊢C SFun S p ->
  G ⊢C Ord0 d -> G ⊢C Fun0 f -> G ⊢C Dom0 f d -> G ⊢C RecOK S p f ->
  G ⊢C Ord0 d' -> G ⊢C Fun0 f' -> G ⊢C Dom0 f' d' -> G ⊢C RecOK S p f' ->
  G ⊢C xi ∈' d -> G ⊢C App0 f xi u -> G ⊢C App0 f' xi u' -> G ⊢C u ≡' u'.
Proof.
  intros Hsl Hsf Hd Hf Hfd Hfr Hd' Hf' Hfd' Hfr' Hx Hu Hu'.
  pose proof (agf_ind HG HR HO S HI p d d' f f' Hsl Hsf Hd Hf Hfd Hfr Hd' Hf' Hfd' Hfr' xi
                (w_ord_el HG HR HO d xi Hd Hx)) as H.
  unfold AgF in H. finst H u u'. fmp H Hu. fmp H Hu'. exact H.
Qed.

(** two recursion functions agree below x when x is contained in both domains *)
Lemma agree_of {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HO : incl Ax_ord G) S
  (HI : incl (rec_insts S) G) p e e' g g' x :
  G ⊢C SLoc S p -> G ⊢C SFun S p ->
  G ⊢C Ord0 e -> G ⊢C Fun0 g -> G ⊢C Dom0 g e -> G ⊢C RecOK S p g ->
  G ⊢C Ord0 e' -> G ⊢C Fun0 g' -> G ⊢C Dom0 g' e' -> G ⊢C RecOK S p g' ->
  G ⊢C Sub0 x e -> G ⊢C Sub0 x e' -> G ⊢C Agree g g' x.
Proof.
  intros Hsl Hsf He Hg Hge Hgr He' Hg' Hge' Hgr' Hx Hx'.
  pose proof (Ax_ord_prim _ HO) as HP.
  unfold Agree. fall z. fintro Hz. fall w. fsplit.
  - fintro Hw. fhave Hze : (sub_use HG HP x e z Hx Hz). fhave Hze' : (sub_use HG HP x e' z Hx' Hz).
    fobtain (w_dom0_app HG HP g' e' z Hge' Hze') as w' Hw'.
    fhave E : (rec_agree0 HG HR HO S HI p e e' g g' z w w' Hsl Hsf He Hg Hge Hgr He' Hg' Hge' Hgr' Hze Hw Hw').
    frew E (App0 g'`[↑] z`[↑] $0). exact Hw'.
  - fintro Hw. fhave Hze : (sub_use HG HP x e z Hx Hz). fhave Hze' : (sub_use HG HP x e' z Hx' Hz).
    fobtain (w_dom0_app HG HP g e z Hge Hze) as w' Hw'.
    fhave E : (rec_agree0 HG HR HO S HI p e e' g g' z w' w Hsl Hsf He Hg Hge Hgr He' Hg' Hge' Hgr' Hze Hw' Hw).
    frew E (App0 g`[↑] z`[↑] $0). exact Hw'.
Qed.

Lemma val_unique {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HO : incl Ax_ord G) S
  (HI : incl (rec_insts S) G) p a v v' :
  G ⊢C SLoc S p -> G ⊢C SFun S p -> G ⊢C Ok S p a v -> G ⊢C Ok S p a v' -> G ⊢C v ≡' v'.
Proof.
  intros Hsl Hsf H1 H2. pose proof (Ax_ord_prim _ HO) as HP.
  okd H1 Ha e g Hoe Hsub Hfun Hdom Hrec Hsr.
  okd H2 Ha' e' g' Hoe' Hsub' Hfun' Hdom' Hrec' Hsr'.
  fhave Hag : (agree_of HG HR HO S HI p e e' g g' a Hsl Hsf Hoe Hfun Hdom Hrec Hoe' Hfun' Hdom' Hrec' Hsub Hsub').
  fhave H : (sloc_use HG HP S p g g' a v Hsl Hfun Hfun' Ha Hag Hsr).
  exact (sfun_use HG HP S p g' a v v' Hsf Hfun' Ha H Hsr').
Qed.

(** ** The existence step: from recursion functions on every ξ ∈ x, one on x *)
Lemma rec_step {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HO : incl Ax_ord G) S
  (HI : incl (rec_insts S) G) p x :
  G ⊢C SLoc S p -> G ⊢C STot S p -> G ⊢C SFun S p -> G ⊢C Ord0 x ->
  G ⊢C ∀ ($0 ∈' x`[↑] → RecFn S p`[↑] $0) -> G ⊢C RecFn S p x.
Proof.
  intros Hsl Hst Hsf Hx IH. pose proof (Ax_ord_prim _ HO) as HP.
  assert (Hfn : forall a b b', G ⊢C (phiR S)[a .: b .: (p .: var)] → (phiR S)[a .: b' .: (p .: var)] → b ≡' b').
  { intros a b b'. unfold phiR. simp. fintro H1. fintro H2. unfold Gr in H1, H2.
    fex H1 v Hv. fdestr Hv Hv1 Hv2. fex H2 v' Hv'. fdestr Hv' Hv1' Hv2'.
    fhave E : (val_unique HG HR HO S HI p a v v' Hsl Hsf Hv2 Hv2').
    frew_in E (OP0 a`[↑] $0 b'`[↑]) Hv1'.
    exact (w_op0_unique HG HP a v b b' Hv1 Hv1'). }
  pose proof (rep_use G 1 (phiR S) (p .: var) x (in_insR S HI) (fb_phiR S) Hfn) as HY.
  unfold phiR in HY. simp_in HY. clear Hfn. fex HY Fg HFg.
  fassert K1 : (∀ (∀ (App0 Fg`[↑]`[↑] $1 $0 → $1 ∈' x`[↑]`[↑] ∧ Ok S p`[↑]`[↑] $1 $0))).
  { fall a. fall v. fintro H. pose proof H as H'. unfold App0 in H'. fex H' q Hq. fdestr Hq Hq1 Hq2.
    pose proof HFg as HFz. finst HFz q. fhave T : (iff_l _ _ _ HFz Hq1). clear HFz.
    fex T a' Ha'. fdestr Ha' Ha'1 Ha'2. unfold Gr in Ha'2. fex Ha'2 v' Hv'. fdestr Hv' Hv'1 Hv'2.
    fhave E : (w_op0_inj HG HP a v a' v' q Hq2 Hv'1). fdestr E E1 E2.
    fsplit.
    - exact (elem_l HG a' a x (eq_sym' HG _ _ E1) Ha'1).
    - frew_in E2 (Ok S p`[↑] a'`[↑] $0) Hv'2. frew_in E1 (Ok S p`[↑] $0 v`[↑]) Hv'2. exact Hv'2. }
  fassert K2 : (∀ (∀ ($1 ∈' x`[↑]`[↑] → Ok S p`[↑]`[↑] $1 $0 → App0 Fg`[↑]`[↑] $1 $0))).
  { fall a. fall v. fintro Ha. fintro Hok. fobtain (w_op0_ex HG HP a v) as q Hq.
    apply (w_app0_intro HG HP Fg a v q Hq). pose proof HFg as HFz. finst HFz q. apply (iff_r _ _ _ HFz).
    fexists a. fsplit; [exact Ha|]. unfold Gr. fexists v. fsplit; [exact Hq|exact Hok]. }
  fassert HFun : (Fun0 Fg).
  { apply (fun0_intro HG HP).
    - apply (isrel0_intro HG HP). fall q. fintro Hq. pose proof HFg as HFz. finst HFz q.
      fhave T : (iff_l _ _ _ HFz Hq). fex T a Ha. fdestr Ha Ha1 Ha2. unfold Gr in Ha2.
      fex Ha2 v Hv. fdestr Hv Hv1 Hv2. fexists a. fexists v. exact Hv1.
    - fall a. fall v. fall v'. fintro H1. fintro H2.
      pose proof K1 as K. finst K a v. fmp K H1. pose proof K1 as K'. finst K' a v'. fmp K' H2.
      exact (val_unique HG HR HO S HI p a v v' Hsl Hsf (CE2 K) (CE2 K')). }
  fassert HDom : (Dom0 Fg x).
  { apply (dom0_intro HG HP).
    - fall a. fintro Ha. pose proof IH as IHa. finst IHa a. fmp IHa Ha. unfold RecFn in IHa.
      fex IHa g Hg. fdestr Hg Hg12 Hg3. fdestr Hg12 Hg1 Hg2.
      fhave Oa : (w_ord_el HG HR HO x a Hx Ha).
      fassert Hall : (∀ ($0 ∈' a`[↑] → ∃ App0 g`[↑]`[↑] $1 $0)).
      { fall z. fintro Hz. exact (w_dom0_app HG HP g a z Hg2 Hz). }
      fhave T : (stot_use HG HP S p g a Hst Hg1 Oa Hall). fex T v Hv.
      fexists v. pose proof K2 as K. finst K a v. fmp K Ha. apply (IE K).
      exact (ok_intro HG S p a v a g Oa Oa (sub_refl0 HG HP a) Hg1 Hg2 Hg3 Hv).
    - fall a. fall v. fintro H. pose proof K1 as K. finst K a v. fmp K H. exact (CE1 K). }
  fassert HRec : (RecOK S p Fg).
  { apply (recok_intro HG HP). fall a. fall v. fintro H.
    pose proof K1 as K. finst K a v. fmp K H. fdestr K Ha Hok.
    okd Hok Oa e g Hoe Hsub Hfun Hdom Hrec Hsr.
    fassert Hag : (Agree g Fg a).
    { unfold Agree. fall z. fintro Hz. fall w.
      fhave Oz : (w_ord_el HG HR HO a z Oa Hz).
      fhave Hze : (sub_use HG HP a e z Hsub Hz).
      fhave Hsz : (w_ord_el_sub HG HR HO z e Hoe Hze).
      fhave Hzx : (w_ord_tr HG HR HO x z a Hx Hz Ha).
      fsplit.
      - fintro Hw.
        fhave Hsr' : (recok_use HG HP S p g z w Hrec Hw).
        fhave Okz : (ok_intro HG S p z w e g Oz Hoe Hsz Hfun Hdom Hrec Hsr').
        pose proof K2 as K'. finst K' z w. fmp K' Hzx. fmp K' Okz. exact K'.
      - fintro Hw. pose proof K1 as K'. finst K' z w. fmp K' Hw. fdestr K' Hzx' Okz.
        fobtain (w_dom0_app HG HP g e z Hdom Hze) as w' Hw'.
        fhave Hsr' : (recok_use HG HP S p g z w' Hrec Hw').
        fhave Okz' : (ok_intro HG S p z w' e g Oz Hoe Hsz Hfun Hdom Hrec Hsr').
        fhave E : (val_unique HG HR HO S HI p z w w' Hsl Hsf Okz Okz').
        frew E (App0 g`[↑] z`[↑] $0). exact Hw'. }
    exact (sloc_use HG HP S p g Fg a v Hsl Hfun HFun Oa Hag Hsr). }
  unfold RecFn. fexists Fg. fsplit; [fsplit|]; [exact HFun|exact HDom|exact HRec].
Qed.

Section Rec.
Context {G : list form} (HG : incl ZF0base G) (HR : In ax_reg' G) (HO : incl Ax_ord G).
Context (S : form) (HS : fb 4 S) (HI : incl (rec_insts S) G).

Theorem rec_ex p d : G ⊢C SLoc S p -> G ⊢C STot S p -> G ⊢C SFun S p -> G ⊢C Ord0 d ->
  G ⊢C ∃ (Fun0 $0 ∧ Dom0 $0 d`[↑] ∧ RecOK S p`[↑] $0).
Proof using All.
  intros Hsl Hst Hsf Hd.
  pose proof (w_ord_ind HG HR HO 1 (psiE S) (p .: var) d (fb_psiE S) (in_insE S HI)) as Hind.
  unfold psiE in Hind. simp_in Hind. change (G ⊢C RecFn S p d). apply Hind; [|exact Hd]. clear Hind.
  fall y. fintro Hy. fintro IHy. exact (rec_step HG HR HO S HI p y Hsl Hst Hsf Hy IHy).
Qed.

Theorem rec_agree p d d' f f' xi u u' : G ⊢C SLoc S p -> G ⊢C SFun S p ->
  G ⊢C Ord0 d -> G ⊢C Fun0 f -> G ⊢C Dom0 f d -> G ⊢C RecOK S p f ->
  G ⊢C Ord0 d' -> G ⊢C Fun0 f' -> G ⊢C Dom0 f' d' -> G ⊢C RecOK S p f' ->
  G ⊢C xi ∈' d -> G ⊢C xi ∈' d' -> G ⊢C App0 f xi u -> G ⊢C App0 f' xi u' -> G ⊢C u ≡' u'.
Proof using All.
  intros Hsl Hsf Hd Hf Hfd Hfr Hd' Hf' Hfd' Hfr' Hx _ Hu Hu'.
  exact (rec_agree0 HG HR HO S HI p d d' f f' xi u u' Hsl Hsf Hd Hf Hfd Hfr Hd' Hf' Hfd' Hfr' Hx Hu Hu').
Qed.

End Rec.
