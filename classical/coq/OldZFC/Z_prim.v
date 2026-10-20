(** * Z_prim: basic theory of the Delta_0 primitives of Z_base (existence, uniqueness,
    equivalence with Std_setbase's predicates, ordered pairs, functions).

    Context convention (all files of zf/zfc): an abstract list [G] of hypotheses with
    [incl ZF0base G] and, where needed, [In ax_reg' G], [In ax_om' G], [incl Ax_X G] for a fixed
    list [Ax_X] of closed separation / replacement instances, and [In inst G] for schema instances.
    Every element of every such list satisfies [ZFR] (proved next to the list). *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_setinf.
From OldRegCon Require MinZF.
From OldZFC Require Import Z_rel Z_base.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

(** the target theory: ZF (library minZFeq, closed schema instances) + regularity *)
Definition ZFR (phi : form) : Prop := ZFc phi \/ phi = MinZF.ax_reg'.
Notation ax_reg' := MinZF.ax_reg'.

Lemma ZFR_base a : In a ZF0base -> ZFR a.
Proof. intros H. left. left. now constructor. Qed.
Lemma ZFR_om : ZFR ax_om'.
Proof. left. now right. Qed.
Lemma ZFR_reg : ZFR ax_reg'.
Proof. now right. Qed.
Lemma ZFR_sep n phi : fb (S n) phi -> ZFR (forall_times n (ax_sep' phi)).
Proof. intros H. left. left. apply ZF0_sep, sep_closed, H. Qed.
Lemma ZFR_rep n phi : fb (S (S n)) phi -> ZFR (forall_times n (ax_rep' phi)).
Proof. intros H. left. left. apply ZF0_rep, rep_closed, H. Qed.

(** fixed instances used by this file (to be filled by the proofs) *)
Definition Ax_prim : list form := [].
Lemma Ax_prim_ok a : In a Ax_prim -> ZFR a.
Proof. intros []. Qed.

(** ** Generic helpers (stated for every context, used inside later proofs) *)
Lemma sing0_to {G} (HG : incl ZF0base G) x s : G ⊢C Sing0 x s -> G ⊢C Sing x s.
Proof.
  intros H. unfold Sing0 in H. fdestr H H1 H2. unfold Sing. fall z. fsplit.
  - fintro Hz. finst H2 z. exact (IE H2 Hz).
  - fintro Hz. fmem.
Qed.

Lemma sing0_of {G} (HG : incl ZF0base G) x s : G ⊢C Sing x s -> G ⊢C Sing0 x s.
Proof.
  intros H. unfold Sing0. fsplit; [exact (sing_in HG x s H)|].
  fall z. fintro Hz. exact (sing_el HG x s z H Hz).
Qed.

Lemma pair0_to {G} (HG : incl ZF0base G) x y p : G ⊢C Pair0 x y p -> G ⊢C is_pair x y p.
Proof.
  intros H. unfold Pair0 in H. fdestr H H12 H3. fdestr H12 H1 H2. unfold is_pair. fall z. fsplit.
  - fintro Hz. finst H3 z. exact (IE H3 Hz).
  - fintro Hz. fcases Hz E1 E2; fmem.
Qed.

Lemma pair0_of {G} (HG : incl ZF0base G) x y p : G ⊢C is_pair x y p -> G ⊢C Pair0 x y p.
Proof.
  intros H. unfold Pair0. fsplit; [fsplit; [exact (pair_l HG x y p H)|exact (pair_r HG x y p H)]|].
  fall z. fintro Hz. exact (pair_el HG x y p z H Hz).
Qed.

Lemma op0_to {G} (HG : incl ZF0base G) x y p : G ⊢C OP0 x y p -> G ⊢C OP x y p.
Proof.
  intros H. unfold OP0 in H. fdestr H H12 H3. fdestr H12 H1 H2. unfold OP. fall z. fsplit.
  - fintro Hz. finst H3 z. fmp H3 Hz. fcases H3 E1 E2.
    + fleft. exact (sing0_to HG x z E1).
    + fright. exact (pair0_to HG x y z E2).
  - fintro Hz. fcases Hz E1 E2.
    + fex H1 s Hs. fdestr Hs Hs1 Hs2. fhave Hs3 : (sing0_to HG x s Hs2).
      fhave E : (sing_unique HG x s z Hs3 E1). fmem.
    + fex H2 s Hs. fdestr Hs Hs1 Hs2. fhave Hs3 : (pair0_to HG x y s Hs2).
      fhave E : (pair_unique HG x y s z Hs3 E2). fmem.
Qed.

Lemma op0_of {G} (HG : incl ZF0base G) x y p : G ⊢C OP x y p -> G ⊢C OP0 x y p.
Proof.
  intros H. unfold OP0. fsplit; [fsplit|].
  - fobtain (sing_ex HG x) as s Hs. fexists s. fsplit.
    + exact (op_in HG x y p s H (DI1 _ Hs)).
    + exact (sing0_of HG x s Hs).
  - fobtain (pair_ex HG x y) as s Hs. fexists s. fsplit.
    + exact (op_in HG x y p s H (DI2 _ Hs)).
    + exact (pair0_of HG x y s Hs).
  - fall z. fintro Hz. fhave E : (op_el HG x y p z H Hz). fcases E E1 E2.
    + fleft. exact (sing0_of HG x z E1).
    + fright. exact (pair0_of HG x y z E2).
Qed.

Lemma app0_to {G} (HG : incl ZF0base G) f u v : G ⊢C App0 f u v -> G ⊢C App f u v.
Proof.
  intros H. unfold App0 in H. fex H p Hp. fdestr Hp Hp1 Hp2.
  apply (app_intro HG f u v p (op0_to HG u v p Hp2) Hp1).
Qed.

Lemma app0_of {G} (HG : incl ZF0base G) f u v : G ⊢C App f u v -> G ⊢C App0 f u v.
Proof.
  intros H. unfold App in H. fex H p Hp. fdestr Hp Hp1 Hp2.
  unfold App0. fexists p. fsplit; [exact Hp2|exact (op0_of HG u v p Hp1)].
Qed.

Lemma emp0_to {G} x : G ⊢C Emp0 x -> G ⊢C is_eset x.
Proof. intros H. exact H. Qed.
Lemma emp0_of {G} x : G ⊢C is_eset x -> G ⊢C Emp0 x.
Proof. intros H. exact H. Qed.
Lemma sub0_to {G} x y : G ⊢C Sub0 x y -> G ⊢C sub' x y.
Proof. intros H. exact H. Qed.
Lemma sub0_of {G} x y : G ⊢C sub' x y -> G ⊢C Sub0 x y.
Proof. intros H. exact H. Qed.

Lemma succ0_to {G} (HG : incl ZF0base G) x s : G ⊢C Succ0 x s -> G ⊢C is_sigma x s.
Proof.
  intros H. unfold Succ0 in H. fdestr H H12 H3. fdestr H12 H1 H2. unfold is_sigma. fall z. fsplit.
  - fintro Hz. finst H3 z. exact (IE H3 Hz).
  - fintro Hz. fcases Hz E1 E2.
    + unfold Sub0 in H2. finst H2 z. exact (IE H2 E1).
    + fmem.
Qed.

Lemma succ0_of {G} (HG : incl ZF0base G) x s : G ⊢C is_sigma x s -> G ⊢C Succ0 x s.
Proof.
  intros H. unfold Succ0. fsplit; [fsplit|].
  - exact (succ_self HG x s H).
  - unfold Sub0. fall z. fintro Hz. exact (succ_in_l HG x s z H Hz).
  - fall z. fintro Hz. exact (succ_el HG x s z H Hz).
Qed.

Lemma union0_to {G} (HG : incl ZF0base G) x u : G ⊢C Union0 x u -> G ⊢C is_union x u.
Proof.
  intros H. unfold Union0 in H. fdestr H H1 H2. unfold is_union. fall z. fsplit.
  - fintro Hz. finst H1 z. exact (IE H1 Hz).
  - fintro Hz. fex Hz y Hy. fdestr Hy Hy1 Hy2. finst H2 y. fmp H2 Hy1. finst H2 z. exact (IE H2 Hy2).
Qed.

Lemma union0_of {G} (HG : incl ZF0base G) x u : G ⊢C is_union x u -> G ⊢C Union0 x u.
Proof.
  intros H. unfold Union0. fsplit.
  - fall z. fintro Hz. exact (union_el HG x u z H Hz).
  - fall y. fintro Hy. fall z. fintro Hz. exact (union_in HG x u y z H Hy Hz).
Qed.

Lemma emp0_unique_g {G} (HG : incl ZF0base G) e e' : G ⊢C Emp0 e -> G ⊢C Emp0 e' -> G ⊢C e ≡' e'.
Proof. intros H1 H2. exact (eset_unique HG e e' H1 H2). Qed.

Lemma op0_unique_g {G} (HG : incl ZF0base G) x y p p' : G ⊢C OP0 x y p -> G ⊢C OP0 x y p' -> G ⊢C p ≡' p'.
Proof.
  intros H1 H2. apply (op0_to HG) in H1, H2. unfold OP in H1, H2. exact (ext_char HG _ p p' H1 H2).
Qed.

Lemma succ0_unique_g {G} (HG : incl ZF0base G) x s s' : G ⊢C Succ0 x s -> G ⊢C Succ0 x s' -> G ⊢C s ≡' s'.
Proof. intros H1 H2. exact (succ_unique HG x s s' (succ0_to HG x s H1) (succ0_to HG x s' H2)). Qed.

Lemma union0_unique_g {G} (HG : incl ZF0base G) x u u' : G ⊢C Union0 x u -> G ⊢C Union0 x u' -> G ⊢C u ≡' u'.
Proof. intros H1 H2. exact (union_unique HG x u u' (union0_to HG x u H1) (union0_to HG x u' H2)). Qed.

Lemma op0_inj_g {G} (HG : incl ZF0base G) x y x' y' p : G ⊢C OP0 x y p -> G ⊢C OP0 x' y' p -> G ⊢C x ≡' x' ∧ y ≡' y'.
Proof.
  intros H1 H2. exact (op_inj HG x y x' y' p p (op0_to HG x y p H1) (op0_to HG x' y' p H2) (eq_refl' HG p)).
Qed.

Lemma op0_comp_g {G} (HG : incl ZF0base G) x y p : G ⊢C OP0 x y p ->
  G ⊢C (∃ ($0 ∈' p`[↑] ∧ x`[↑] ∈' $0)) ∧ ∃ ($0 ∈' p`[↑] ∧ y`[↑] ∈' $0).
Proof.
  intros H. unfold OP0 in H. fdestr H H12 H3. fdestr H12 H1 H2. fsplit.
  - fex H1 s Hs. fdestr Hs Hs1 Hs2. fexists s. fsplit; [exact Hs1|]. unfold Sing0 in Hs2. exact (CE1 Hs2).
  - fex H2 s Hs. fdestr Hs Hs1 Hs2. fexists s. fsplit; [exact Hs1|]. unfold Pair0 in Hs2. exact (CE2 (CE1 Hs2)).
Qed.

Lemma pairsall_use_g {G} (HG : incl ZF0base G) f B u v : G ⊢C PairsAll f B -> G ⊢C App0 f u v -> G ⊢C B[v .: u .: var].
Proof.
  intros H Ha. unfold App0 in Ha. fex Ha p Hp. fdestr Hp Hpf Hop.
  fhave T : (op0_comp_g HG u v p Hop). fdestr T T1 T2. fex T1 s Hs. fdestr Hs Hs1 Hs2.
  fex T2 s' Hs'. fdestr Hs' Hs'1 Hs'2.
  unfold PairsAll in H. finst H p. fmp H Hpf. finst H s. fmp H Hs1. finst H u. fmp H Hs2.
  finst H s'. fmp H Hs'1. finst H v. fmp H Hs'2. fmp H Hop.
  rewrite !subst_comp in H. erewrite subst_ext; [exact H|]. intros [|[|k]]; cbn; try reflexivity.
  - now autorewrite with fsub.
  - replace (k + 5) with (S (S (S (S (S k))))) by lia. cbn. now autorewrite with fsub.
Qed.

Lemma pairsall_intro_g {G} (HG : incl ZF0base G) f B :
  (forall G' u v, incl G G' -> G' ⊢C App0 f u v -> G' ⊢C B[v .: u .: var]) -> G ⊢C PairsAll f B.
Proof.
  intros H. assert (HGG : incl G G) by (intros a Ha; exact Ha).
  unfold PairsAll. fall p. fintro Hp. fall s. fintro Hs. fall u. fintro Hu. fall s'. fintro Hs'.
  fall v. fintro Hv. fintro Hop.
  match goal with |- ?G' ⊢C _ => assert (Ha : G' ⊢C App0 f u v) end.
  { unfold App0. fexists p. fsplit; assumption. }
  specialize (H _ u v HGG Ha).
  rewrite !subst_comp. erewrite subst_ext; [exact H|]. intros [|[|k]]; cbn; try reflexivity.
  - now autorewrite with fsub.
  - replace (k + 5) with (S (S (S (S (S k))))) by lia. cbn. now autorewrite with fsub.
Qed.

Lemma app0_intro_g {G} f u v p : G ⊢C OP0 u v p -> G ⊢C p ∈' f -> G ⊢C App0 f u v.
Proof. intros H1 H2. unfold App0. fexists p. fsplit; assumption. Qed.

Lemma isrel0_el_g {G} (HG : incl ZF0base G) f p : G ⊢C IsRel0 f -> G ⊢C p ∈' f -> G ⊢C ∃ ∃ OP0 $1 $0 p`[↑]`[↑].
Proof.
  intros H Hp. unfold IsRel0 in H. finst H p. fmp H Hp. fex H s Hs. fdestr Hs Hs1 Hs2.
  fex Hs2 u Hu. fdestr Hu Hu1 Hu2. fex Hu2 s' Hs'. fdestr Hs' Hs'1 Hs'2. fex Hs'2 v Hv. fdestr Hv Hv1 Hv2.
  fexists u. fexists v. exact Hv2.
Qed.

Lemma dom0_app_g {G} (HG : incl ZF0base G) f d u : G ⊢C Dom0 f d -> G ⊢C u ∈' d -> G ⊢C ∃ App0 f`[↑] u`[↑] $0.
Proof.
  intros H Hu. unfold Dom0 in H. fdestr H H1 H2. finst H1 u. fmp H1 Hu.
  fex H1 p Hp. fdestr Hp Hp1 Hp2. fex Hp2 s Hs. fdestr Hs Hs1 Hs2. fex Hs2 v Hv. fdestr Hv Hv1 Hv2.
  fexists v. exact (app0_intro_g f u v p Hv2 Hp1).
Qed.

Lemma dom0_in_g {G} (HG : incl ZF0base G) f d u v : G ⊢C Dom0 f d -> G ⊢C App0 f u v -> G ⊢C u ∈' d.
Proof.
  intros H Ha. unfold Dom0 in H. fdestr H H1 H2. pose proof (pairsall_use_g HG f _ u v H2 Ha) as T.
  simp_in T. exact T.
Qed.

Lemma fun0_app_g {G} (HG : incl ZF0base G) f u v v' : G ⊢C Fun0 f -> G ⊢C App0 f u v -> G ⊢C App0 f u v' -> G ⊢C v ≡' v'.
Proof.
  intros H H1 H2. unfold Fun0 in H. fdestr H Hr Hp. pose proof (pairsall_use_g HG f _ u v Hp H1) as T.
  simp_in T. pose proof (pairsall_use_g HG f _ u v' T H2) as T'. simp_in T'.
  fmp T' (eq_refl' HG u). exact T'.
Qed.

Section Prim.
Context {G : list form} (HG : incl ZF0base G) (HP : incl Ax_prim G).

(** ** Equivalences with Std_setbase *)
Lemma Sing0_iff x s : G ⊢C Sing0 x s ↔ Sing x s.
Proof. fsplit; fintro H; [exact (sing0_to HG x s H)|exact (sing0_of HG x s H)]. Qed.
Lemma Pair0_iff x y p : G ⊢C Pair0 x y p ↔ is_pair x y p.
Proof. fsplit; fintro H; [exact (pair0_to HG x y p H)|exact (pair0_of HG x y p H)]. Qed.
Lemma OP0_iff x y p : G ⊢C OP0 x y p ↔ OP x y p.
Proof. fsplit; fintro H; [exact (op0_to HG x y p H)|exact (op0_of HG x y p H)]. Qed.
Lemma App0_iff f u v : G ⊢C App0 f u v ↔ App f u v.
Proof. fsplit; fintro H; [exact (app0_to HG f u v H)|exact (app0_of HG f u v H)]. Qed.
Lemma Emp0_iff x : G ⊢C Emp0 x ↔ is_eset x.
Proof. fsplit; fintro H; exact H. Qed.
Lemma Sub0_iff x y : G ⊢C Sub0 x y ↔ sub' x y.
Proof. fsplit; fintro H; exact H. Qed.
Lemma Succ0_iff x s : G ⊢C Succ0 x s ↔ is_sigma x s.
Proof. fsplit; fintro H; [exact (succ0_to HG x s H)|exact (succ0_of HG x s H)]. Qed.
Lemma Union0_iff x u : G ⊢C Union0 x u ↔ is_union x u.
Proof. fsplit; fintro H; [exact (union0_to HG x u H)|exact (union0_of HG x u H)]. Qed.

(** ** Existence and uniqueness *)
Lemma emp0_ex : G ⊢C ∃ Emp0 $0.
Proof. exact (eset_ex HG). Qed.
Lemma sing0_ex x : G ⊢C ∃ Sing0 x`[↑] $0.
Proof. fobtain (sing_ex HG x) as s Hs. fexists s. exact (sing0_of HG x s Hs). Qed.
Lemma pair0_ex x y : G ⊢C ∃ Pair0 x`[↑] y`[↑] $0.
Proof. fobtain (pair_ex HG x y) as s Hs. fexists s. exact (pair0_of HG x y s Hs). Qed.
Lemma op0_ex x y : G ⊢C ∃ OP0 x`[↑] y`[↑] $0.
Proof. fobtain (op_ex HG x y) as s Hs. fexists s. exact (op0_of HG x y s Hs). Qed.
Lemma succ0_ex x : G ⊢C ∃ Succ0 x`[↑] $0.
Proof. fobtain (succ_ex HG x) as s Hs. fexists s. exact (succ0_of HG x s Hs). Qed.
Lemma union0_ex x : G ⊢C ∃ Union0 x`[↑] $0.
Proof. fobtain (union_ex HG x) as s Hs. fexists s. exact (union0_of HG x s Hs). Qed.

Lemma emp0_unique e e' : G ⊢C Emp0 e -> G ⊢C Emp0 e' -> G ⊢C e ≡' e'.
Proof. exact (emp0_unique_g HG e e'). Qed.
Lemma op0_unique x y p p' : G ⊢C OP0 x y p -> G ⊢C OP0 x y p' -> G ⊢C p ≡' p'.
Proof. exact (op0_unique_g HG x y p p'). Qed.
Lemma succ0_unique x s s' : G ⊢C Succ0 x s -> G ⊢C Succ0 x s' -> G ⊢C s ≡' s'.
Proof. exact (succ0_unique_g HG x s s'). Qed.
Lemma union0_unique x u u' : G ⊢C Union0 x u -> G ⊢C Union0 x u' -> G ⊢C u ≡' u'.
Proof. exact (union0_unique_g HG x u u'). Qed.

(** ** Ordered pairs *)
Lemma op0_inj x y x' y' p : G ⊢C OP0 x y p -> G ⊢C OP0 x' y' p -> G ⊢C x ≡' x' ∧ y ≡' y'.
Proof. exact (op0_inj_g HG x y x' y' p). Qed.
(** the components of p are bounded by p, as used in [PairsAll] *)
Lemma op0_comp x y p : G ⊢C OP0 x y p ->
  G ⊢C (∃ ($0 ∈' p`[↑] ∧ x`[↑] ∈' $0)) ∧ ∃ ($0 ∈' p`[↑] ∧ y`[↑] ∈' $0).
Proof. exact (op0_comp_g HG x y p). Qed.
Lemma op0_comp' x y p : G ⊢C OP0 x y p ->
  G ⊢C (∃ ($0 ∈' p`[↑] ∧ x`[↑] ∈' $0)) ∧ ∃ ($0 ∈' p`[↑] ∧ y`[↑] ∈' $0).
Proof. exact (op0_comp_g HG x y p). Qed.

(** ** PairsAll: introduction and elimination *)
Lemma pairsall_use f B u v : G ⊢C PairsAll f B -> G ⊢C App0 f u v -> G ⊢C B[v .: u .: var].
Proof. exact (pairsall_use_g HG f B u v). Qed.
Lemma pairsall_intro f B :
  (forall G' u v, incl G G' -> G' ⊢C App0 f u v -> G' ⊢C B[v .: u .: var]) -> G ⊢C PairsAll f B.
Proof. exact (pairsall_intro_g HG f B). Qed.

(** ** Functions *)
Lemma fun0_app f u v v' : G ⊢C Fun0 f -> G ⊢C App0 f u v -> G ⊢C App0 f u v' -> G ⊢C v ≡' v'.
Proof. exact (fun0_app_g HG f u v v'). Qed.
Lemma dom0_app f d u : G ⊢C Dom0 f d -> G ⊢C u ∈' d -> G ⊢C ∃ App0 f`[↑] u`[↑] $0.
Proof. exact (dom0_app_g HG f d u). Qed.
Lemma dom0_in f d u v : G ⊢C Dom0 f d -> G ⊢C App0 f u v -> G ⊢C u ∈' d.
Proof. exact (dom0_in_g HG f d u v). Qed.
Lemma app0_intro f u v p : G ⊢C OP0 u v p -> G ⊢C p ∈' f -> G ⊢C App0 f u v.
Proof. exact (app0_intro_g f u v p). Qed.
Lemma isrel0_el f p : G ⊢C IsRel0 f -> G ⊢C p ∈' f -> G ⊢C ∃ ∃ OP0 $1 $0 p`[↑]`[↑].
Proof. exact (isrel0_el_g HG f p). Qed.

End Prim.
