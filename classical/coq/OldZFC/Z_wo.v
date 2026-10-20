(** * Z_wo: each L_α carries a well-order, hence every family in L_α has a choice set (in ZF).

    The axiom of choice used throughout (Zermelo's form, no pairs needed):
      ∀x [ (∀y∈x ∃z z∈y) → (∀y∈x ∀y'∈x (y ≠ y' → ¬∃z (z∈y ∧ z∈y'))) →
           ∃c ∀y∈x ∃z (z∈y ∧ z∈c ∧ ∀w (w∈y → w∈c → w = z)) ]

    Proof (plain ZF + regularity, no relativization): a well-order W_ξ of L_{ξ+1} = Def(L_ξ) is built
    canonically by transfinite recursion (Z_trec) with the step formula [Sout]:
    - L_ξ is ordered rank-first: by the least η with z ∈ L_{η+1}, then by W_η ([RhoOrd], [sf_wo]);
    - B_0 = L_ξ ∪ {L_ξ} is ordered with L_ξ first and L_ξ last ([Sum0], [sum_wo]);
    - an inner recursion over ω ([Sin]) carries (B_n, W_n) with B_{n+1} = Step(B_n): the old
      elements first, then the new ones by their least construction (k, a, b, c) ([NxR], [code_min]);
      B_n is the n-th stage of Cl(B_0) ([inner_inv]);
    - Def(L_ξ) ⊆ Cl(B_0) is ordered stage-first ([CstOrd], [cst_wo]).
    Orders are sets of ordered pairs ([PairSet]); [WO W X] = W is asymmetric on X and every nonempty
    subset of X has a W-least element.  The choice set of x ∈ L_α is {least element of y | y ∈ x}. *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_setinf.
From OldZFC Require Import Z_rel Z_base Z_prim Z_ord Z_trec Z_cl Z_L.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Create HintDb wsub.

Definition ACmat (x : term) : form :=
  (∀ ($0 ∈' x`[↑] → ∃ ($0 ∈' $1))) →
  (∀ ($0 ∈' x`[↑] → ∀ ($0 ∈' x`[↑]`[↑] → ¬ ($1 ≡' $0) → ¬ ∃ ($0 ∈' $2 ∧ $0 ∈' $1)))) →
  ∃ ∀ ($0 ∈' x`[↑]`[↑] → ∃ ($0 ∈' $1 ∧ $0 ∈' $2 ∧ ∀ ($0 ∈' $2 → $0 ∈' $3 → $0 ≡' $1))).
#[global] Arguments ACmat : simpl never.
Lemma ACmat_subst x sg : (ACmat x)[sg] = ACmat x`[sg].
Proof. psubst ACmat. Qed.
#[global] Hint Rewrite ACmat_subst : fsub wsub.

Definition ax_ac : form := ∀ ACmat $0.

Lemma ax_ac_closed : closedf ax_ac.
Proof. unfold ax_ac, ACmat, closedf. cbn. lia. Qed.

(** ** Generic instantiation of a formula with 4 / 5 arguments *)
Definition I4 (phi : form) (a b c d : term) : form := phi[a .: b .: c .: d .: (fun _ => a)].
Definition I5 (phi : form) (a b c d e : term) : form := phi[a .: b .: c .: d .: e .: (fun _ => a)].
#[global] Arguments I4 : simpl never.
#[global] Arguments I5 : simpl never.
Lemma I4_subst phi a b c d sg : (I4 phi a b c d)[sg] = I4 phi a`[sg] b`[sg] c`[sg] d`[sg].
Proof. unfold I4. rewrite subst_comp. apply subst_ext. intros [|[|[|[|n]]]]; reflexivity. Qed.
Lemma I5_subst phi a b c d e sg : (I5 phi a b c d e)[sg] = I5 phi a`[sg] b`[sg] c`[sg] d`[sg] e`[sg].
Proof. unfold I5. rewrite subst_comp. apply subst_ext. intros [|[|[|[|[|n]]]]]; reflexivity. Qed.
#[global] Hint Rewrite I4_subst I5_subst : fsub wsub.

(** ** Sets of ordered pairs given by a formula.
    [PairSet B W phi]: W = {(z, z') | z, z' ∈ B, phi}, where in [phi] $1 = z, $0 = z' and
    $(k+2) = the outer variable $k. *)
Definition PairSet (B W : term) (phi : form) : form :=
  ∀ ($0 ∈' W`[↑] ↔ ∃ ($0 ∈' B`[↑]`[↑] ∧ ∃ ($0 ∈' B`[↑]`[↑]`[↑] ∧ (OP0 $1 $0 $2 ∧ phi[$0 .: $1 .: (fun k => $(3 + k))])))).
#[global] Arguments PairSet : simpl never.
Lemma PairSet_subst B W phi sg : (PairSet B W phi)[sg] = PairSet B`[sg] W`[sg] (phi[up (up sg)]).
Proof.
  unfold PairSet. cbn. autorewrite with fsub. cbn. fix_up. rewrite !subst_comp.
  match goal with |- _ = ?R => match R with context [phi[?s2]] => erewrite (@subst_ext _ _ _ _ phi _ s2) end end;
    [reflexivity|]. intros [|[|k]]; cbn; try reflexivity. unfold funcomp.
  rewrite !subst_term_comp. apply subst_term_ext. intros n. cbn. reflexivity.
Qed.
#[global] Hint Rewrite PairSet_subst : fsub wsub.

(** the separation formula for [PairSet]: $0 = p, $1 = B, $(k+2) = outer variable k of phi *)
Definition PSF (phi : form) : form :=
  ∃ ($0 ∈' $2 ∧ ∃ ($0 ∈' $3 ∧ (OP0 $1 $0 $2 ∧ phi[$0 .: $1 .: (fun k => $(4 + k))]))).

(** ** Well-orders given as sets of ordered pairs *)
(** m is the W-least element of y *)
Definition Lst (W y m : term) : form := m ∈' y ∧ ∀ ($0 ∈' y`[↑] → ¬ ($0 ≡' m`[↑]) → App0 W`[↑] m`[↑] $0).
(** W well-orders X: asymmetric on X, and every nonempty subset of X has a W-least element *)
Definition WO (W X : term) : form :=
  (∀ ($0 ∈' X`[↑] → ∀ ($0 ∈' X`[↑]`[↑] → App0 W`[↑]`[↑] $1 $0 → App0 W`[↑]`[↑] $0 $1 → ⊥))) ∧
  ∀ (Sub0 $0 X`[↑] → (∃ ($0 ∈' $1)) → ∃ Lst W`[↑]`[↑] $1 $0).
#[global] Arguments Lst : simpl never.
#[global] Arguments WO : simpl never.
Lemma Lst_subst W y m sg : (Lst W y m)[sg] = Lst W`[sg] y`[sg] m`[sg].
Proof. psubst Lst. Qed.
#[global] Hint Rewrite Lst_subst : fsub wsub.
Lemma WO_subst W X sg : (WO W X)[sg] = WO W`[sg] X`[sg].
Proof. psubst WO. Qed.
#[global] Hint Rewrite WO_subst : fsub wsub.

(** ordered sum: the elements of Y first (ordered by O), then the others (ordered by r) *)
Definition SumR (Y O : term) (r : form) (z z' : term) : form :=
  ((((z ∈' Y ∧ z' ∈' Y) ∧ App0 O z z') ∨ (z ∈' Y ∧ ¬ (z' ∈' Y))) ∨ (((¬ (z ∈' Y)) ∧ (¬ (z' ∈' Y))) ∧ r)).
#[global] Arguments SumR : simpl never.
Lemma SumR_subst Y O r z z' sg : (SumR Y O r z z')[sg] = SumR Y`[sg] O`[sg] r[sg] z`[sg] z'`[sg].
Proof. unfold SumR. cbn. now autorewrite with fsub. Qed.
#[global] Hint Rewrite SumR_subst : fsub wsub.

(** stage-first order: rank (by [Rk]: $0 = z, $1 = rank, $2 = P, $3 = Q) first, then, inside a
    rank e, by [Ow] ($0 = z, $1 = z', $2 = e, $3 = P, $4 = Q) *)
Definition SFR (Rk Ow : form) (P Q z z' : term) : form :=
  ∃ ∃ ((I4 Rk z`[↑]`[↑] $1 P`[↑]`[↑] Q`[↑]`[↑] ∧ I4 Rk z'`[↑]`[↑] $0 P`[↑]`[↑] Q`[↑]`[↑]) ∧
       ($1 ∈' $0 ∨ ($1 ≡' $0 ∧ I5 Ow z`[↑]`[↑] z'`[↑]`[↑] $1 P`[↑]`[↑] Q`[↑]`[↑]))).
#[global] Arguments SFR : simpl never.
Lemma SFR_subst Rk Ow P Q z z' sg : (SFR Rk Ow P Q z z')[sg] = SFR Rk Ow P`[sg] Q`[sg] z`[sg] z'`[sg].
Proof. psubst SFR. Qed.
#[global] Hint Rewrite SFR_subst : fsub wsub.


(** ** The code order on the new elements of Step(B), given an order W of B *)
(** t = op_k(a, b, c) for some a, b, c ∈ B *)
Definition HasK (k : nat) (B t : term) : form :=
  ∃ ($0 ∈' B`[↑] ∧ ∃ ($0 ∈' B`[↑]`[↑] ∧ ∃ ($0 ∈' B`[↑]`[↑]`[↑] ∧ Op k $2 $1 $0 t`[↑]`[↑]`[↑]))).
#[global] Arguments HasK : simpl never.
Lemma HasK_subst k B t sg : (HasK k B t)[sg] = HasK k B`[sg] t`[sg].
Proof. psubst HasK. Qed.
#[global] Hint Rewrite HasK_subst : fsub wsub.

(** t has no construction of kind < k *)
Fixpoint NB (k : nat) (B t : term) : form :=
  match k with 0 => ¬ ⊥ | S j => NB j B t ∧ ¬ (HasK j B t) end.
#[global] Arguments NB : simpl never.
Lemma NB_S k B t : NB (S k) B t = (NB k B t ∧ ¬ (HasK k B t)).
Proof. reflexivity. Qed.
Lemma NB_subst k B t sg : (NB k B t)[sg] = NB k B`[sg] t`[sg].
Proof. induction k as [|k IH]; [reflexivity|]. rewrite !NB_S. cbn. now rewrite IH, HasK_subst. Qed.
#[global] Hint Rewrite NB_subst : fsub wsub.

Definition Lex3 (W a b c a' b' c' : term) : form :=
  App0 W a a' ∨ (a ≡' a' ∧ (App0 W b b' ∨ (b ≡' b' ∧ App0 W c c'))).
#[global] Arguments Lex3 : simpl never.
Lemma Lex3_subst W a b c a' b' c' sg :
  (Lex3 W a b c a' b' c')[sg] = Lex3 W`[sg] a`[sg] b`[sg] c`[sg] a'`[sg] b'`[sg] c'`[sg].
Proof. psubst Lex3. Qed.
#[global] Hint Rewrite Lex3_subst : fsub wsub.

(** some construction of t of kind k is below all constructions of t' of kind k *)
Definition COk (k : nat) (B W t t' : term) : form :=
  ∃ ($0 ∈' B`[↑] ∧ ∃ ($0 ∈' B`[↑]`[↑] ∧ ∃ ($0 ∈' B`[↑]`[↑]`[↑] ∧ (Op k $2 $1 $0 t`[↑]`[↑]`[↑] ∧
    ∀ ($0 ∈' B`[↑]`[↑]`[↑]`[↑] → ∀ ($0 ∈' B`[↑]`[↑]`[↑]`[↑]`[↑] → ∀ ($0 ∈' B`[↑]`[↑]`[↑]`[↑]`[↑]`[↑] →
       Op k $2 $1 $0 t'`[↑]`[↑]`[↑]`[↑]`[↑]`[↑] → Lex3 W`[↑]`[↑]`[↑]`[↑]`[↑]`[↑] $5 $4 $3 $2 $1 $0))))))).
#[global] Arguments COk : simpl never.
Lemma COk_subst k B W t t' sg : (COk k B W t t')[sg] = COk k B`[sg] W`[sg] t`[sg] t'`[sg].
Proof. psubst COk. Qed.
#[global] Hint Rewrite COk_subst : fsub wsub.

Definition Clause (k : nat) (B W t t' : term) : form :=
  (HasK k B t ∧ NB k B t) ∧ (NB k B t' ∧ ((¬ (HasK k B t')) ∨ COk k B W t t')).
#[global] Arguments Clause : simpl never.
Lemma Clause_subst k B W t t' sg : (Clause k B W t t')[sg] = Clause k B`[sg] W`[sg] t`[sg] t'`[sg].
Proof. psubst Clause. Qed.
#[global] Hint Rewrite Clause_subst : fsub wsub.

Fixpoint NewOrd (k : nat) (B W t t' : term) : form :=
  match k with 0 => ⊥ | S j => NewOrd j B W t t' ∨ Clause j B W t t' end.
#[global] Arguments NewOrd : simpl never.
Lemma NewOrd_S k B W t t' : NewOrd (S k) B W t t' = (NewOrd k B W t t' ∨ Clause k B W t t').
Proof. reflexivity. Qed.
Lemma NewOrd_subst k B W t t' sg : (NewOrd k B W t t')[sg] = NewOrd k B`[sg] W`[sg] t`[sg] t'`[sg].
Proof. induction k as [|k IH]; [reflexivity|]. rewrite !NewOrd_S. cbn. now rewrite IH, Clause_subst. Qed.
#[global] Hint Rewrite NewOrd_subst : fsub wsub.

(** the order of the new elements: $0 = t, $1 = t', $2 = B, $3 = W *)
Definition NOf : form := NewOrd 8 $2 $3 $0 $1.

(** separation formulas for the code minimization *)
Definition A1P (k : nat) (a T B : term) : form :=
  ∃ ($0 ∈' T`[↑] ∧ ∃ ($0 ∈' B`[↑]`[↑] ∧ ∃ ($0 ∈' B`[↑]`[↑]`[↑] ∧ Op k a`[↑]`[↑]`[↑] $1 $0 $2))).
Definition A2P (k : nat) (b T B a : term) : form :=
  ∃ ($0 ∈' T`[↑] ∧ ∃ ($0 ∈' B`[↑]`[↑] ∧ Op k a`[↑]`[↑] b`[↑]`[↑] $0 $1)).
Definition A3P (k : nat) (c T a b : term) : form :=
  ∃ ($0 ∈' T`[↑] ∧ Op k a`[↑] b`[↑] c`[↑] $0).
#[global] Arguments A1P : simpl never.
#[global] Arguments A2P : simpl never.
#[global] Arguments A3P : simpl never.
Lemma A1P_subst k a T B sg : (A1P k a T B)[sg] = A1P k a`[sg] T`[sg] B`[sg].
Proof. psubst A1P. Qed.
Lemma A2P_subst k b T B a sg : (A2P k b T B a)[sg] = A2P k b`[sg] T`[sg] B`[sg] a`[sg].
Proof. psubst A2P. Qed.
Lemma A3P_subst k c T a b sg : (A3P k c T a b)[sg] = A3P k c`[sg] T`[sg] a`[sg] b`[sg].
Proof. psubst A3P. Qed.
#[global] Hint Rewrite A1P_subst A2P_subst A3P_subst : fsub wsub.

(** ** The inner recursion over ω: values are pairs (B_n, W_n) *)
(** B' = Step B and W' its order (B first by W, then the new elements by the code order) *)
Definition NxR (B W B' W' : term) : form :=
  Step B B' ∧ PairSet B' W' (SumR B`[↑]`[↑] W`[↑]`[↑] (I4 NOf $1 $0 B`[↑]`[↑] W`[↑]`[↑]) $1 $0).
#[global] Arguments NxR : simpl never.
Lemma NxR_subst B W B' W' sg : (NxR B W B' W')[sg] = NxR B`[sg] W`[sg] B'`[sg] W'`[sg].
Proof. psubst NxR. Qed.
#[global] Hint Rewrite NxR_subst : fsub wsub.

(** v = (Step B, W') where u = (B, W); v = ∅ if u is not a pair *)
Definition NextP (u v : term) : form :=
  (∃ (∃ (OP0 $1 $0 u`[↑]`[↑] ∧ ∃ (∃ (OP0 $1 $0 v`[↑]`[↑]`[↑]`[↑] ∧ NxR $3 $2 $1 $0))))) ∨
  ((∀ (∀ (¬ (OP0 $1 $0 u`[↑]`[↑])))) ∧ Emp0 v).
#[global] Arguments NextP : simpl never.
Lemma NextP_subst u v sg : (NextP u v)[sg] = NextP u`[sg] v`[sg].
Proof. psubst NextP. Qed.
#[global] Hint Rewrite NextP_subst : fsub wsub.

(** step formula: f = $0, ξ = $1, v = $2, p = $3 (the start pair (B_0, W_0)) *)
Definition Sin : form :=
  (Emp0 $1 → $2 ≡' $3) ∧ (∀ ($0 ∈' $2 → Succ0 $0 $2 → ∃ (App0 $2 $1 $0 ∧ NextP $0 $4))) ∧ (Lim0 $1 → Emp0 $2).

(** z ∈ B_n where h(n) = (B_n, W_n) *)
Definition InB (h n z : term) : form :=
  ∃ (App0 h`[↑] n`[↑] $0 ∧ ∃ (∃ (OP0 $1 $0 $2 ∧ z`[↑]`[↑]`[↑] ∈' $1))).
(** n is the stage of z *)
Definition St (h n z : term) : form := InB h n z ∧ ∀ ($0 ∈' n`[↑] → ¬ InB h`[↑] $0 z`[↑]).
(** (z, z') ∈ W_n *)
Definition AppW (h n z z' : term) : form :=
  ∃ (App0 h`[↑] n`[↑] $0 ∧ ∃ (∃ (OP0 $1 $0 $2 ∧ App0 $0 z`[↑]`[↑]`[↑] z'`[↑]`[↑]`[↑]))).
#[global] Arguments InB : simpl never.
#[global] Arguments St : simpl never.
#[global] Arguments AppW : simpl never.
Lemma InB_subst h n z sg : (InB h n z)[sg] = InB h`[sg] n`[sg] z`[sg].
Proof. psubst InB. Qed.
#[global] Hint Rewrite InB_subst : fsub wsub.
Lemma St_subst h n z sg : (St h n z)[sg] = St h`[sg] n`[sg] z`[sg].
Proof. psubst St. Qed.
Lemma AppW_subst h n z z' sg : (AppW h n z z')[sg] = AppW h`[sg] n`[sg] z`[sg] z'`[sg].
Proof. psubst AppW. Qed.
#[global] Hint Rewrite St_subst AppW_subst : fsub wsub.

(** rank and order for the stage-first order on Cl: $0 = z, $1 = n / $1 = z', $2 = n; P = h, Q = ω *)
Definition RkI : form := $1 ∈' $3 ∧ St $2 $1 $0.
Definition OwI : form := AppW $3 $2 $0 $1.

(** ** The outer recursion over the ordinals *)
(** z ∈ L_{e+1} *)
Definition InL1 (z e : term) : form := ∃ (Succ0 e`[↑] $0 ∧ ∃ (LL $1 $0 ∧ z`[↑]`[↑] ∈' $0)).
(** e is the least ordinal with z ∈ L_{e+1} *)
Definition Rho (z e : term) : form := InL1 z e ∧ ∀ ($0 ∈' e`[↑] → ¬ InL1 z`[↑] $0).
#[global] Arguments InL1 : simpl never.
#[global] Arguments Rho : simpl never.
Lemma InL1_subst z e sg : (InL1 z e)[sg] = InL1 z`[sg] e`[sg].
Proof. psubst InL1. Qed.
#[global] Hint Rewrite InL1_subst : fsub wsub.
Lemma Rho_subst z e sg : (Rho z e)[sg] = Rho z`[sg] e`[sg].
Proof. psubst Rho. Qed.
#[global] Hint Rewrite Rho_subst : fsub wsub.

(** $0 = z, $1 = e, $2 = ξ, $3 = F;  $0 = z, $1 = z', $2 = e, $3 = ξ, $4 = F *)
Definition RkO : form := $1 ∈' $2 ∧ Rho $0 $1.
Definition OwO : form := ∃ (App0 $5 $3 $0 ∧ App0 $0 $1 $2).

(** pieces of the outer step *)
Definition RhoOrd (xi F Y O : term) : form := PairSet Y O (SFR RkO OwO xi`[↑]`[↑] F`[↑]`[↑] $1 $0).
Definition Sum0 (Y O B W0 : term) : form := PairSet B W0 (SumR Y`[↑]`[↑] O`[↑]`[↑] (I4 ⊥ $1 $0 Y`[↑]`[↑] Y`[↑]`[↑]) $1 $0).
Definition InSeq (q w h : term) : form := (Fun0 h ∧ Dom0 h w) ∧ RecOK Sin q h.
Definition CstOrd (h w D v : term) : form := PairSet D v (SFR RkI OwI h`[↑]`[↑] w`[↑]`[↑] $1 $0).
#[global] Arguments RhoOrd : simpl never.
#[global] Arguments Sum0 : simpl never.
#[global] Arguments InSeq : simpl never.
#[global] Arguments CstOrd : simpl never.
Lemma RhoOrd_subst xi F Y O sg : (RhoOrd xi F Y O)[sg] = RhoOrd xi`[sg] F`[sg] Y`[sg] O`[sg].
Proof. psubst RhoOrd. Qed.
Lemma Sum0_subst Y O B W0 sg : (Sum0 Y O B W0)[sg] = Sum0 Y`[sg] O`[sg] B`[sg] W0`[sg].
Proof. psubst Sum0. Qed.
Lemma InSeq_subst q w h sg : (InSeq q w h)[sg] = InSeq q`[sg] w`[sg] h`[sg].
Proof. psubst InSeq. Qed.
Lemma CstOrd_subst h w D v sg : (CstOrd h w D v)[sg] = CstOrd h`[sg] w`[sg] D`[sg] v`[sg].
Proof. psubst CstOrd. Qed.
#[global] Hint Rewrite RhoOrd_subst Sum0_subst InSeq_subst CstOrd_subst : fsub wsub.

(** v = the canonical order of L_{ξ+1} = Def(L_ξ), computed from F (the orders of L_{η+1}, η < ξ):
    Y = L_ξ, O = rank-first order of Y, B = Y ∪ {Y}, W0 = O followed by Y, q = (B, W0),
    h = inner recursion from q, D = Def(Y), v = stage-first order of D *)
Definition OutP (F xi v : term) : form :=
  ∃ (LL xi`[↑] $0 ∧
   ∃ (RhoOrd xi`[↑]`[↑] F`[↑]`[↑] $1 $0 ∧
    ∃ (Succ0 $2 $0 ∧
     ∃ (Sum0 $3 $2 $1 $0 ∧
      ∃ (OP0 $2 $1 $0 ∧
       ∃ (Om0 $0 ∧
        ∃ (InSeq $2 $1 $0 ∧
         ∃ (Def0 $7 $0 ∧ CstOrd $1 $2 $0 v`[↑]`[↑]`[↑]`[↑]`[↑]`[↑]`[↑]`[↑])))))))).
#[global] Arguments OutP : simpl never.
Lemma OutP_subst F xi v sg : (OutP F xi v)[sg] = OutP F`[sg] xi`[sg] v`[sg].
Proof. psubst OutP. Qed.
#[global] Hint Rewrite OutP_subst : fsub wsub.

Definition Sout : form := OutP $0 $1 $2.

(** the induction formula: $0 = ξ, $1 = F, $2 = d *)
Definition PsiP (F d xi : term) : form :=
  xi ∈' d → ∀ (App0 F`[↑] xi`[↑] $0 → ∀ (LL xi`[↑]`[↑] $0 → ∀ (Def0 $1 $0 → WO $2 $0))).
#[global] Arguments PsiP : simpl never.
Lemma PsiP_subst F d xi sg : (PsiP F d xi)[sg] = PsiP F`[sg] d`[sg] xi`[sg].
Proof. psubst PsiP. Qed.
#[global] Hint Rewrite PsiP_subst : fsub wsub.

(** further instance formulas *)
Definition LRf (Rk : form) : form := ∃ ($0 ∈' $2 ∧ I4 Rk $0 $1 $3 $4).
Definition SRf (Rk : form) : form := I4 Rk $0 $1 $2 $3.
Definition InL1f : form := InL1 $1 $0.
Definition InBf : form := InB $1 $0 $2.
Definition InvF : form := ∃ (App0 $2 $1 $0 ∧ ∃ (∃ (OP0 $1 $0 $2 ∧ (WO $0 $1 ∧ App0 $5 $3 $1)))).
Definition ChF : form := ∃ ($0 ∈' $2 ∧ Lst $3 $0 $1).
Definition phRho : form := SFR RkO OwO $2 $3 $1 $0.
Definition phSum0 : form := SumR $2 $3 (I4 ⊥ $1 $0 $2 $2) $1 $0.
Definition phNext : form := SumR $2 $3 (I4 NOf $1 $0 $2 $3) $1 $0.
Definition phCst : form := SFR RkI OwI $2 $3 $1 $0.
Definition psi_ind : form := PsiP $1 $2 $0.

Definition code_insts : list form :=
  flat_map (fun k => [forall_times 2 (ax_sep' (A1P k $0 $1 $2)); forall_times 3 (ax_sep' (A2P k $0 $1 $2 $3));
                      forall_times 3 (ax_sep' (A3P k $0 $1 $2 $3))]) (seq 0 8).

(** ** Instances *)
Definition sepin_f : form := $0 ∈' $1.
Definition wo_insts1 : list form :=
  [forall_times 1 (ax_sep' sepin_f);
   forall_times 3 (ax_sep' (PSF phRho)); forall_times 3 (ax_sep' (PSF phSum0));
   forall_times 3 (ax_sep' (PSF phNext)); forall_times 3 (ax_sep' (PSF phCst));
   forall_times 1 (ax_sep' InL1f);
   forall_times 3 (ax_sep' (LRf RkO)); forall_times 3 (ax_sep' (LRf RkI));
   forall_times 3 (ax_sep' (SRf RkO)); forall_times 3 (ax_sep' (SRf RkI));
   forall_times 2 (ax_sep' InBf);
   forall_times 2 (ax_sep' (¬ psi_ind));
   forall_times 2 (ax_sep' InvF);
   forall_times 2 (ax_sep' ChF)].
Definition wo_list : list form := rec_insts Sin ++ rec_insts Sout ++ wo_insts1 ++ code_insts.
Definition Ax_wo : list form := Ax_L ++ wo_list.


Lemma Ax_wo_ok a : In a Ax_wo -> ZFR a.
Proof.
  unfold Ax_wo. intros [H|H]%in_app_iff; [now apply Ax_L_ok|].
  unfold wo_list in H. rewrite !in_app_iff in H. destruct H as [H|[H|[H|H]]].
  - exact (rec_insts_ok Sin a ltac:(fbcomp) H).
  - exact (rec_insts_ok Sout a ltac:(fbcomp) H).
  - unfold wo_insts1 in H.
    repeat match goal with
           | H : In _ (_ :: _) |- _ => destruct H as [<-|H]; [apply ZFR_sep; fbcomp|]
           | H : In _ nil |- _ => destruct H
           end.
  - unfold code_insts in H. apply in_flat_map in H as [k [_ H]].
    destruct H as [<-|[<-|[<-|[]]]]; apply ZFR_sep; destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; fbcomp.
Qed.
Lemma Ax_wo_L G : incl Ax_wo G -> incl Ax_L G.
Proof. intros H a Ha. apply H, in_app_iff. now left. Qed.
Definition WOx (G : list form) : Prop := In ax_reg' G /\ In ax_om' G /\ incl Ax_wo G.
Lemma WOx_cons G a : WOx G -> WOx (a :: G).
Proof. intros (H1 & H2 & H3). split; [now right|split; [now right|]]. intros b Hb. right. now apply H3. Qed.

(** a smaller rewrite database for this file's substitution normalization (faster than fsub) *)
#[local] Hint Rewrite up_term subst_term_shift shift_scons_term subst_term_var : wsub.
#[local] Hint Rewrite shift_scons_form subst_shift up_form_comm subst_var up_inst_form : wsub.
#[local] Hint Rewrite sub'_subst is_power_subst : wsub.
#[local] Hint Rewrite Sing0_subst Pair0_subst OP0_subst Emp0_subst Sub0_subst Trans0_subst Ord0_subst Succ0_subst
  Lim0_subst Om0_subst Union0_subst App0_subst PairsAll_subst IsRel0_subst Fun0_subst Dom0_subst : wsub.
#[local] Hint Rewrite SR_subst RecOK_subst Agree_subst : wsub.
#[local] Hint Rewrite Ext0_subst PJ_subst SC_subst AI_subst AE_subst Op_subst Ops_subst OpsIn_subst Step_subst
  RanU_subst Cl_subst Def0_subst : wsub.
#[local] Hint Rewrite LL_subst LimU_subst : wsub.
#[local] Ltac simp ::= cbn; autorewrite with wsub; cbn; autorewrite with wsub; fix_up.
#[local] Ltac simp_in H ::= cbn in H; autorewrite with wsub in H; cbn in H; autorewrite with wsub in H; fix_up_in H.

#[local] Ltac weaken_facts a G ::=
  repeat match goal with
  | H : G ⊢C _ |- _ => apply (weak_cons G a) in H
  | H : forall k : nat, @prv _ _ _ class G (@?P k) |- _ =>
      let H' := fresh in pose proof (fun k => weak_cons G a _ (H k)) as H'; clear H; rename H' into H
  | H : incl _ G |- _ => apply (incl_cons_r _ G a) in H
  | H : In _ G |- _ => apply (in_cons_r _ a G) in H
  | H : WOx G |- _ => apply (WOx_cons G a) in H
  end.

Lemma WOx_L G : WOx G -> incl Ax_L G.
Proof. intros (_ & _ & H) a Ha. apply H, in_app_iff. now left. Qed.

#[local] Ltac ctxs := match goal with HX : WOx ?G |- _ =>
  let HR := fresh "HR" in let HOm := fresh "HOm" in let HW := fresh "HW" in
  pose proof HX as [HR [HOm HW]];
  let HL := fresh "HL" in pose proof (WOx_L _ HX) as HL;
  let HC := fresh "HC" in pose proof (Ax_L_cl _ HL) as HC;
  let HO := fresh "HO" in pose proof (Ax_cl_ord _ HC) as HO;
  let HP := fresh "HP" in pose proof (Ax_ord_prim _ HO) as HP end.
#[local] Ltac wr X := intros; ctxs; eapply X; eassumption.
#[local] Ltac getin X := match goal with |- ?G' ⊢C _ => assert (X : In _ G') end.

#[local] Set Default Proof Using "All".

(** ** Wrappers for upstream lemmas (robust w.r.t. their section hypotheses) *)
Section W.
Context {G : list form} (HG : incl ZF0base G) (HX : WOx G).

Lemma w_op0_ex x y : G ⊢C ∃ OP0 x`[↑] y`[↑] $0.  Proof. wr @op0_ex. Qed.
Lemma w_op0_unique x y p p' : G ⊢C OP0 x y p -> G ⊢C OP0 x y p' -> G ⊢C p ≡' p'.  Proof. wr @op0_unique. Qed.
Lemma w_op0_inj x y x' y' p : G ⊢C OP0 x y p -> G ⊢C OP0 x' y' p -> G ⊢C x ≡' x' ∧ y ≡' y'.  Proof. wr @op0_inj. Qed.
Lemma w_app0_intro f u v p : G ⊢C OP0 u v p -> G ⊢C p ∈' f -> G ⊢C App0 f u v.  Proof. wr @app0_intro. Qed.
Lemma w_fun0_app f u v v' : G ⊢C Fun0 f -> G ⊢C App0 f u v -> G ⊢C App0 f u v' -> G ⊢C v ≡' v'.  Proof. wr @fun0_app. Qed.
Lemma w_dom0_app f d u : G ⊢C Dom0 f d -> G ⊢C u ∈' d -> G ⊢C ∃ App0 f`[↑] u`[↑] $0.  Proof. wr @dom0_app. Qed.
Lemma w_dom0_in f d u v : G ⊢C Dom0 f d -> G ⊢C App0 f u v -> G ⊢C u ∈' d.  Proof. wr @dom0_in. Qed.
Lemma w_isrel0_el f p : G ⊢C IsRel0 f -> G ⊢C p ∈' f -> G ⊢C ∃ ∃ OP0 $1 $0 p`[↑]`[↑].  Proof. wr @isrel0_el. Qed.
Lemma w_pairsall_use f B u v : G ⊢C PairsAll f B -> G ⊢C App0 f u v -> G ⊢C B[v .: u .: var].  Proof. wr @pairsall_use. Qed.
Lemma w_union0_ex x : G ⊢C ∃ Union0 x`[↑] $0.  Proof. wr @union0_ex. Qed.
Lemma w_succ0_ex x : G ⊢C ∃ Succ0 x`[↑] $0.  Proof. wr @succ0_ex. Qed.
Lemma w_succ0_unique x s s' : G ⊢C Succ0 x s -> G ⊢C Succ0 x s' -> G ⊢C s ≡' s'.  Proof. wr @succ0_unique. Qed.
Lemma w_emp0_ex : G ⊢C ∃ Emp0 $0.  Proof. wr @emp0_ex. Qed.

Lemma w_no_self x : G ⊢C x ∈' x -> G ⊢C ⊥.  Proof. wr @no_self. Qed.
Lemma w_no_cycle2 x y : G ⊢C x ∈' y -> G ⊢C y ∈' x -> G ⊢C ⊥.  Proof. wr @no_cycle2. Qed.
Lemma w_ord_el a x : G ⊢C Ord0 a -> G ⊢C x ∈' a -> G ⊢C Ord0 x.  Proof. wr @ord_el. Qed.
Lemma w_ord_tr a x y : G ⊢C Ord0 a -> G ⊢C x ∈' y -> G ⊢C y ∈' a -> G ⊢C x ∈' a.  Proof. wr @ord_tr. Qed.
Lemma w_ord_tri a b : G ⊢C Ord0 a -> G ⊢C Ord0 b -> G ⊢C a ∈' b ∨ a ≡' b ∨ b ∈' a.  Proof. wr @ord_tri. Qed.
Lemma w_ord_succ a s : G ⊢C Ord0 a -> G ⊢C Succ0 a s -> G ⊢C Ord0 s.  Proof. wr @ord_succ. Qed.
Lemma w_ord_cases a : G ⊢C Ord0 a -> G ⊢C Emp0 a ∨ (∃ (Ord0 $0 ∧ Succ0 $0 a`[↑])) ∨ Lim0 a.  Proof. wr @ord_cases. Qed.
Lemma w_om_ex : G ⊢C ∃ Om0 $0.  Proof. wr @om_ex. Qed.
Lemma w_om_unique w w' : G ⊢C Om0 w -> G ⊢C Om0 w' -> G ⊢C w ≡' w'.  Proof. wr @om_unique. Qed.
Lemma w_om_ord w : G ⊢C Om0 w -> G ⊢C Ord0 w.  Proof. wr @om_ord. Qed.
Lemma w_om_emp w e : G ⊢C Om0 w -> G ⊢C Emp0 e -> G ⊢C e ∈' w.  Proof. wr @om_emp. Qed.
Lemma w_om_succ w n s : G ⊢C Om0 w -> G ⊢C n ∈' w -> G ⊢C Succ0 n s -> G ⊢C s ∈' w.  Proof. wr @om_succ. Qed.
Lemma w_om_ind w X : G ⊢C Om0 w -> G ⊢C ∀ (Emp0 $0 → $0 ∈' X`[↑]) ->
  G ⊢C ∀ ($0 ∈' w`[↑] → $0 ∈' X`[↑] → ∀ (Succ0 $1 $0 → $0 ∈' X`[↑]`[↑])) -> G ⊢C Sub0 w X.
Proof. wr @om_ind. Qed.
Lemma w_least_ord n psi sg a : fb (S n) psi -> In (least_inst n psi) G ->
  G ⊢C Ord0 a -> G ⊢C psi[a .: sg] ->
  G ⊢C ∃ (Ord0 $0 ∧ psi[up sg] ∧ ∀ ($0 ∈' $1 → ¬ psi[up (sg >> subst_term ↑)])).
Proof. wr @least_ord. Qed.
Lemma w_ord_ind n psi sg a : fb (S n) psi -> In (least_inst n (¬ psi)) G ->
  G ⊢C ∀ (Ord0 $0 → (∀ ($0 ∈' $1 → psi[up (sg >> subst_term ↑)])) → psi[up sg]) ->
  G ⊢C Ord0 a -> G ⊢C psi[a .: sg].
Proof. wr @ord_ind. Qed.

Lemma w_rec_ex S (HS : fb 4 S) (HI : incl (rec_insts S) G) p d : G ⊢C SLoc S p -> G ⊢C STot S p -> G ⊢C SFun S p -> G ⊢C Ord0 d ->
  G ⊢C ∃ (Fun0 $0 ∧ Dom0 $0 d`[↑] ∧ RecOK S p`[↑] $0).
Proof. wr @rec_ex. Qed.
Lemma w_rec_agree S (HS : fb 4 S) (HI : incl (rec_insts S) G) p d d' f f' xi u u' : G ⊢C SLoc S p -> G ⊢C SFun S p ->
  G ⊢C Ord0 d -> G ⊢C Fun0 f -> G ⊢C Dom0 f d -> G ⊢C RecOK S p f ->
  G ⊢C Ord0 d' -> G ⊢C Fun0 f' -> G ⊢C Dom0 f' d' -> G ⊢C RecOK S p f' ->
  G ⊢C xi ∈' d -> G ⊢C xi ∈' d' -> G ⊢C App0 f xi u -> G ⊢C App0 f' xi u' -> G ⊢C u ≡' u'.
Proof.
  intros H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14. ctxs.
  eapply rec_agree with (d := d) (d' := d') (f := f) (f' := f') (xi := xi); eassumption.
Qed.

Lemma w_step_ex X : G ⊢C ∃ Step X`[↑] $0.  Proof. wr @step_ex. Qed.
Lemma w_step_unique X Y Y' : G ⊢C Step X Y -> G ⊢C Step X Y' -> G ⊢C Y ≡' Y'.  Proof. wr @step_unique. Qed.
Lemma w_def_ex A : G ⊢C ∃ Def0 A`[↑] $0.  Proof. wr @def_ex. Qed.
Lemma w_def_unique A D D' : G ⊢C Def0 A D -> G ⊢C Def0 A D' -> G ⊢C D ≡' D'.  Proof. wr @def_unique. Qed.
Lemma w_def_trans A D : G ⊢C Trans0 A -> G ⊢C Def0 A D -> G ⊢C Sub0 A D.  Proof. wr @def_trans. Qed.

Lemma w_LL_ex a : G ⊢C Ord0 a -> G ⊢C ∃ LL a`[↑] $0.  Proof. wr @LL_ex. Qed.
Lemma w_LL_unique a Y Y' : G ⊢C Ord0 a -> G ⊢C LL a Y -> G ⊢C LL a Y' -> G ⊢C Y ≡' Y'.  Proof. wr @LL_unique. Qed.
Lemma w_LL_zero a Y : G ⊢C Emp0 a -> G ⊢C LL a Y -> G ⊢C Emp0 Y.  Proof. wr @LL_zero. Qed.
Lemma w_LL_succ a s Y Y' : G ⊢C Ord0 a -> G ⊢C Succ0 a s -> G ⊢C LL a Y -> G ⊢C LL s Y' -> G ⊢C Def0 Y Y'.  Proof. wr @LL_succ. Qed.
Lemma w_LL_lim l Y : G ⊢C Lim0 l -> G ⊢C LL l Y ->
  G ⊢C ∀ ($0 ∈' Y`[↑] → ∃ ($0 ∈' l`[↑]`[↑] ∧ ∃ (LL $1 $0 ∧ $2 ∈' $0))).
Proof. wr @LL_lim. Qed.
Lemma w_LL_mono a b Ya Yb : G ⊢C Ord0 a -> G ⊢C b ∈' a -> G ⊢C LL a Ya -> G ⊢C LL b Yb ->
  G ⊢C Yb ∈' Ya ∧ Sub0 Yb Ya.
Proof. wr @LL_mono. Qed.
Lemma w_LL_trans a Y : G ⊢C Ord0 a -> G ⊢C LL a Y -> G ⊢C Trans0 Y.  Proof. wr @LL_trans. Qed.

End W.

(** ** Small tactics *)
#[local] Ltac fneg := match goal with H : _ ⊢C (?a → ⊥), H' : _ ⊢C ?a |- _ => apply Exp; exact (IE H H') end.

(** ** Basic lemmas *)
Lemma wo_sub0_use {G} (HG : incl ZF0base G) x y z : G ⊢C Sub0 x y -> G ⊢C z ∈' x -> G ⊢C z ∈' y.
Proof. intros H Hz. unfold Sub0 in H. finst H z. exact (IE H Hz). Qed.

Lemma lst_in {G} W y m : G ⊢C Lst W y m -> G ⊢C m ∈' y.
Proof. intros H. exact (CE1 H). Qed.
Lemma lst_lt {G} W y m u : G ⊢C Lst W y m -> G ⊢C u ∈' y -> G ⊢C ¬ (u ≡' m) -> G ⊢C App0 W m u.
Proof. intros H Hu Hn. pose proof (CE2 H) as H2. finst H2 u. exact (IE (IE H2 Hu) Hn). Qed.

Lemma wo_asym {G} W X a b : G ⊢C WO W X -> G ⊢C a ∈' X -> G ⊢C b ∈' X -> G ⊢C App0 W a b -> G ⊢C App0 W b a -> G ⊢C ⊥.
Proof.
  intros H Ha Hb H1 H2. unfold WO in H. pose proof (CE1 H) as H3. finst H3 a. fmp H3 Ha. finst H3 b.
  fmp H3 Hb. fmp H3 H1. exact (IE H3 H2).
Qed.
Lemma wo_least {G} W X y u : G ⊢C WO W X -> G ⊢C Sub0 y X -> G ⊢C u ∈' y -> G ⊢C ∃ Lst W`[↑] y`[↑] $0.
Proof.
  intros H Hy Hu. unfold WO in H. pose proof (CE2 H) as H4. finst H4 y. fmp H4 Hy. apply (IE H4).
  fexists u. exact Hu.
Qed.
Lemma lst_unique {G} (HG : incl ZF0base G) W X y m m' : G ⊢C WO W X -> G ⊢C Sub0 y X ->
  G ⊢C Lst W y m -> G ⊢C Lst W y m' -> G ⊢C m ≡' m'.
Proof.
  intros H Hy H1 H2. fcontra Hne.
  fassert N1 : (¬ (m' ≡' m)). { fintro E. apply (IE Hne). feq. }
  pose proof (lst_lt W y m m' H1 (lst_in W y m' H2) N1) as A1.
  pose proof (lst_lt W y m' m H2 (lst_in W y m H1) Hne) as A2.
  exact (wo_asym W X m m' H (wo_sub0_use HG _ _ _ Hy (lst_in _ _ _ H1)) (wo_sub0_use HG _ _ _ Hy (lst_in _ _ _ H2)) A1 A2).
Qed.
Lemma wo_sub {G} (HG : incl ZF0base G) W X X' : G ⊢C WO W X -> G ⊢C Sub0 X' X -> G ⊢C WO W X'.
Proof.
  intros H HX'. unfold WO. fsplit.
  - fall a. fintro Ha. fall b. fintro Hb. fintro H1. fintro H2.
    exact (wo_asym W X a b H (wo_sub0_use HG _ _ _ HX' Ha) (wo_sub0_use HG _ _ _ HX' Hb) H1 H2).
  - fall y. fintro Hy. fintro Hne. fex Hne u Hu.
    fassert Hy' : (Sub0 y X). { unfold Sub0. fall z. fintro Hz. apply (wo_sub0_use HG _ _ _ HX'). exact (wo_sub0_use HG _ _ _ Hy Hz). }
    exact (wo_least W X y u H Hy' Hu).
Qed.

(** ** PairSet *)
Lemma pairset_el {G} (HG : incl ZF0base G) (HX : WOx G) B W phi z z' : G ⊢C PairSet B W phi -> G ⊢C App0 W z z' ->
  G ⊢C (z ∈' B ∧ z' ∈' B) ∧ phi[z' .: z .: var].
Proof.
  intros H Hz. unfold App0 in Hz. fex Hz p Hp. fdestr Hp Hp1 Hp2.
  unfold PairSet in H. finst H p. pose proof (iff_l _ _ _ H Hp1) as T. clear H.
  fex T a Ha. fdestr Ha Ha1 Ha2. fex Ha2 b Hb. fdestr Hb Hb1 Hb2. fdestr Hb2 Hb3 Hb4.
  pose proof (w_op0_inj HG HX _ _ _ _ _ Hp2 Hb3) as E. fdestr E E1 E2.
  fsplit; [fsplit; fmem|].
  rewrite !subst_comp in Hb4. eapply leib_gen; [exact HG| |exact Hb4].
  intros [|[|k]]; cbn; unfold funcomp; cbn; rewrite ?subst_term_shift, ?shift_scons_term; try feq; apply (eq_refl' HG).
Qed.

Lemma pairset_in {G} (HG : incl ZF0base G) (HX : WOx G) B W phi z z' : G ⊢C PairSet B W phi ->
  G ⊢C z ∈' B -> G ⊢C z' ∈' B -> G ⊢C phi[z' .: z .: var] -> G ⊢C App0 W z z'.
Proof.
  intros H Hz Hz' Hp. fobtain (w_op0_ex HG HX z z') as p Hpp.
  apply (w_app0_intro HG HX W z z' p Hpp).
  unfold PairSet in H. finst H p. apply (iff_r _ _ _ H). fexists z. fsplit; [exact Hz|].
  fexists z'. fsplit; [exact Hz'|]. fsplit; [exact Hpp|].
  rewrite !subst_comp. erewrite subst_ext; [exact Hp|].
  intros [|[|k]]; cbn; unfold funcomp; cbn; rewrite ?subst_term_shift, ?shift_scons_term; reflexivity.
Qed.

Lemma pairset_unique {G} (HG : incl ZF0base G) B W W' phi : G ⊢C PairSet B W phi -> G ⊢C PairSet B W' phi -> G ⊢C W ≡' W'.
Proof. intros H1 H2. unfold PairSet in H1, H2. exact (ext_char HG _ W W' H1 H2). Qed.

Lemma fb_PSF n phi : fb (2 + n) phi -> fb (S (S n)) (PSF phi).
Proof.
  intros H. unfold PSF, OP0, Sing0, Pair0. cbn. repeat split; try lia.
  eapply fb_subst; [exact H|]. intros [|[|i]] Hi; cbn; lia.
Qed.

Lemma pairset_ex {G} (HG : incl ZF0base G) n phi sg B : fb (2 + n) phi -> In (forall_times (S n) (ax_sep' (PSF phi))) G ->
  G ⊢C ∃ PairSet B`[↑] $0 (phi[up (up (sg >> subst_term ↑))]).
Proof.
  intros Hfb Hin.
  assert (HPw : G ⊢C ax_power') by (apply Ctx, in_power, HG).
  pose proof HPw as T. finst T B. fex T PB HPB.
  pose proof HPw as T. finst T PB. fex T PPB HPPB. clear HPw.
  pose proof (sep_use _ (S n) (PSF phi) (B .: sg) PPB Hin (fb_PSF n phi Hfb)) as T.
  fex T Sx HS. fexists Sx. unfold PairSet. fall p. fsplit.
  - fintro Hp. finst HS p. pose proof (CE2 (iff_l _ _ _ HS Hp)) as T. clear HS.
    unfold PSF in T. simp_in T. fex T z Hz. fdestr Hz Hz1 Hz2. fex Hz2 z' Hz'. fdestr Hz' Hz3 Hz4. fdestr Hz4 Hop Hph.
    fexists z. fsplit; [exact Hz1|]. fexists z'. fsplit; [exact Hz3|]. fsplit; [exact Hop|].
    rewrite !subst_comp in Hph |- *. erewrite subst_ext; [exact Hph|].
    intros [|[|k]]; cbn; unfold funcomp; cbn; rewrite ?subst_term_comp; try reflexivity; apply subst_term_ext; intros; reflexivity.
  - fintro Hp. fex Hp z Hz. fdestr Hz Hz1 Hz2. fex Hz2 z' Hz'. fdestr Hz' Hz3 Hz4. fdestr Hz4 Hop Hph.
    finst HS p. apply (iff_r _ _ _ HS). fsplit.
    + unfold is_power in HPPB. finst HPPB p. apply (iff_r _ _ _ HPPB). unfold sub'. fall s. fintro Hs.
      unfold is_power in HPB. finst HPB s. apply (iff_r _ _ _ HPB). unfold sub'. fall t. fintro Ht.
      unfold OP0 in Hop. pose proof (CE2 Hop) as Hop3. finst Hop3 s. fmp Hop3 Hs.
      fcases Hop3 Hs1 Hs2.
      * unfold Sing0 in Hs1. pose proof (CE2 Hs1) as T. finst T t. fmp T Ht. fmem.
      * unfold Pair0 in Hs2. pose proof (CE2 Hs2) as T. finst T t. fmp T Ht. fcases T T1 T2; fmem.
    + unfold PSF. simp. fexists z. fsplit; [exact Hz1|]. fexists z'. fsplit; [exact Hz3|]. fsplit; [exact Hop|].
      rewrite !subst_comp in Hph |- *. erewrite subst_ext; [exact Hph|].
      intros [|[|k]]; cbn; unfold funcomp; cbn; rewrite ?subst_term_comp; try reflexivity; apply subst_term_ext; intros; reflexivity.
Qed.

Lemma in_wo {G} (HX : WOx G) a : In a wo_list -> In a G.
Proof. intros H. apply (proj2 (proj2 HX)). unfold Ax_wo. apply in_app_iff. now right. Qed.
#[local] Ltac inwo := match goal with HX : WOx _ |- In _ _ =>
  apply (in_wo HX); unfold wo_list, wo_insts1; rewrite ?in_app_iff; cbn -[forall_times ax_sep' rec_insts code_insts]; solve [intuition auto] end.

(** ** Ordered sums *)
Lemma sum_wo {G} (HG : incl ZF0base G) (HX : WOx G) (Rn : form) X Y W1 W P Q :
  G ⊢C Sub0 Y X -> G ⊢C WO W1 Y ->
  G ⊢C ∀ (Sub0 $0 X`[↑] → (∀ ($0 ∈' $1 → ¬ ($0 ∈' Y`[↑]`[↑]))) → (∃ ($0 ∈' $1)) →
          ∃ ($0 ∈' $1 ∧ ∀ ($0 ∈' $2 → ¬ ($0 ≡' $1) → I4 Rn $1 $0 P`[↑]`[↑]`[↑] Q`[↑]`[↑]`[↑]))) ->
  G ⊢C ∀ ($0 ∈' X`[↑] → ∀ ($0 ∈' X`[↑]`[↑] → ¬ ($1 ∈' Y`[↑]`[↑]) → ¬ ($0 ∈' Y`[↑]`[↑]) →
          I4 Rn $1 $0 P`[↑]`[↑] Q`[↑]`[↑] → I4 Rn $0 $1 P`[↑]`[↑] Q`[↑]`[↑] → ⊥)) ->
  G ⊢C ∀ ($0 ∈' X`[↑] → ∀ ($0 ∈' X`[↑]`[↑] →
          (App0 W`[↑]`[↑] $1 $0 ↔ SumR Y`[↑]`[↑] W1`[↑]`[↑] (I4 Rn $1 $0 P`[↑]`[↑] Q`[↑]`[↑]) $1 $0))) ->
  G ⊢C WO W X.
Proof.
  intros HYX HW1 HP2 Has Hch. unfold WO. fsplit.
  - fall a. fintro Ha. fall b. fintro Hb. fintro H1. fintro H2.
    pose proof Hch as C1. finst C1 a. fmp C1 Ha. finst C1 b. fmp C1 Hb. pose proof (iff_l _ _ _ C1 H1) as S1. clear C1.
    pose proof Hch as C2. finst C2 b. fmp C2 Hb. finst C2 a. fmp C2 Ha. pose proof (iff_l _ _ _ C2 H2) as S2. clear C2.
    unfold SumR in S1, S2.
    fcases S1 S1a S1b; [fcases S1a S1c S1d|]; (fcases S2 S2a S2b; [fcases S2a S2c S2d|]).
    + fdestr S1c S1e S1f. fdestr S1e S1g S1h. fdestr S2c S2e S2f. exact (wo_asym W1 Y a b HW1 S1g S1h S1f S2f).
    + fdestr S1c S1e S1f. fdestr S1e S1g S1h. fdestr S2d S2e S2f. fneg.
    + fdestr S1c S1e S1f. fdestr S1e S1g S1h. fdestr S2b S2e S2f. fdestr S2e S2g S2h. fneg.
    + fdestr S1d S1e S1f. fdestr S2c S2e S2f. fdestr S2e S2g S2h. fneg.
    + fdestr S1d S1e S1f. fdestr S2d S2e S2f. fneg.
    + fdestr S1d S1e S1f. fdestr S2b S2e S2f. fdestr S2e S2g S2h. fneg.
    + fdestr S1b S1e S1f. fdestr S1e S1g S1h. fdestr S2c S2e S2f. fdestr S2e S2i S2j. fneg.
    + fdestr S1b S1e S1f. fdestr S1e S1g S1h. fdestr S2d S2e S2f. fneg.
    + fdestr S1b S1e S1f. fdestr S1e S1g S1h. fdestr S2b S2e S2f.
      finst Has a. fmp Has Ha. finst Has b. fmp Has Hb. fmp Has S1g. fmp Has S1h. fmp Has S1f. exact (IE Has S2f).
  - fall T. fintro HT. fintro Hne.
    apply (XM_rule _ (∃ ($0 ∈' T`[↑] ∧ $0 ∈' Y`[↑]))).
    + fintro HTY.
      match goal with |- ?G' ⊢C _ => assert (Hin : In (forall_times 1 (ax_sep' sepin_f)) G') by inwo end.
      pose proof (sep_use _ 1 sepin_f (Y .: var) T Hin ltac:(fbcomp)) as HS. unfold sepin_f in HS. simp_in HS.
      fex HS T0 HT0.
      fassert HT0Y : (Sub0 T0 Y).
      { unfold Sub0. fall t. fintro Ht. pose proof HT0 as H. finst H t. exact (CE2 (iff_l _ _ _ H Ht)). }
      fex HTY t Ht. fdestr Ht Ht1 Ht2.
      fassert Ht0 : (t ∈' T0). { pose proof HT0 as H. finst H t. apply (iff_r _ _ _ H). fsplit; assumption. }
      pose proof (wo_least W1 Y T0 t HW1 HT0Y Ht0) as T1. fex T1 m Hm.
      pose proof HT0 as H. finst H m. pose proof (iff_l _ _ _ H (lst_in _ _ _ Hm)) as Hm1. clear H. fdestr Hm1 HmT HmY.
      fexists m. unfold Lst. fsplit; [exact HmT|]. fall u. fintro Hu. fintro Hum.
      pose proof Hch as C. finst C m. fmp C (wo_sub0_use HG _ _ _ HT HmT). finst C u. fmp C (wo_sub0_use HG _ _ _ HT Hu).
      apply (iff_r _ _ _ C). unfold SumR. apply (XM_rule _ (u ∈' Y)).
      * fintro HuY. fleft. fleft. fsplit; [fsplit; assumption|]. apply (lst_lt W1 T0 m u Hm); [|exact Hum].
        pose proof HT0 as H. finst H u. apply (iff_r _ _ _ H). fsplit; assumption.
      * fintro HuY. fleft. fright. fsplit; assumption.
    + fintro HnTY.
      fassert HnY : (∀ ($0 ∈' T`[↑] → ¬ ($0 ∈' Y`[↑]))).
      { fall t. fintro Ht. fintro HtY. apply (IE HnTY). fexists t. fsplit; assumption. }
      pose proof HP2 as H. finst H T. fmp H HT. fmp H HnY. fmp H Hne. fex H m Hm. fdestr Hm HmT Hm2.
      fexists m. unfold Lst. fsplit; [exact HmT|]. fall u. fintro Hu. fintro Hum.
      pose proof Hch as C. finst C m. fmp C (wo_sub0_use HG _ _ _ HT HmT). finst C u. fmp C (wo_sub0_use HG _ _ _ HT Hu).
      apply (iff_r _ _ _ C). unfold SumR. fright. fsplit; [fsplit|].
      * pose proof HnY as H. finst H m. exact (IE H HmT).
      * pose proof HnY as H. finst H u. exact (IE H Hu).
      * finst Hm2 u. fmp Hm2 Hu. exact (IE Hm2 Hum).
Qed.

(** ** Stage-first orders *)
Lemma sf_wo {G} (HG : incl ZF0base G) (HX : WOx G) (Rk Ow : form) X W P Q :
  G ⊢C ∀ ($0 ∈' X`[↑] → ∃ (Ord0 $0 ∧ I4 Rk $1 $0 P`[↑]`[↑] Q`[↑]`[↑])) ->
  G ⊢C ∀ ($0 ∈' X`[↑] → ∀ (∀ (I4 Rk $2 $1 P`[↑]`[↑]`[↑] Q`[↑]`[↑]`[↑] → I4 Rk $2 $0 P`[↑]`[↑]`[↑] Q`[↑]`[↑]`[↑] → $1 ≡' $0))) ->
  G ⊢C ∀ (Sub0 $0 X`[↑] → (∃ ($0 ∈' $1)) →
     ∃ ((Ord0 $0 ∧ ∃ ($0 ∈' $2 ∧ I4 Rk $0 $1 P`[↑]`[↑]`[↑] Q`[↑]`[↑]`[↑])) ∧
        ∀ ($0 ∈' $1 → ¬ ∃ ($0 ∈' $3 ∧ I4 Rk $0 $1 P`[↑]`[↑]`[↑]`[↑] Q`[↑]`[↑]`[↑]`[↑])))) ->
  G ⊢C ∀ (∀ (∃ (∀ ($0 ∈' $1 ↔ $0 ∈' $3 ∧ I4 Rk $0 $2 P`[↑]`[↑]`[↑]`[↑] Q`[↑]`[↑]`[↑]`[↑])))) ->
  G ⊢C ∀ (Ord0 $0 → ∀ ((∀ ($0 ∈' $1 → $0 ∈' X`[↑]`[↑]`[↑] ∧ I4 Rk $0 $2 P`[↑]`[↑]`[↑] Q`[↑]`[↑]`[↑])) → (∃ ($0 ∈' $1)) →
            ∃ ($0 ∈' $1 ∧ ∀ ($0 ∈' $2 → ¬ ($0 ≡' $1) → I5 Ow $1 $0 $3 P`[↑]`[↑]`[↑]`[↑] Q`[↑]`[↑]`[↑]`[↑])))) ->
  G ⊢C ∀ (Ord0 $0 → ∀ ($0 ∈' X`[↑]`[↑] → ∀ ($0 ∈' X`[↑]`[↑]`[↑] →
            I4 Rk $1 $2 P`[↑]`[↑]`[↑] Q`[↑]`[↑]`[↑] → I4 Rk $0 $2 P`[↑]`[↑]`[↑] Q`[↑]`[↑]`[↑] →
            I5 Ow $1 $0 $2 P`[↑]`[↑]`[↑] Q`[↑]`[↑]`[↑] → I5 Ow $0 $1 $2 P`[↑]`[↑]`[↑] Q`[↑]`[↑]`[↑] → ⊥))) ->
  G ⊢C ∀ ($0 ∈' X`[↑] → ∀ ($0 ∈' X`[↑]`[↑] → (App0 W`[↑]`[↑] $1 $0 ↔ SFR Rk Ow P`[↑]`[↑] Q`[↑]`[↑] $1 $0))) ->
  G ⊢C WO W X.
Proof.
  intros H1 H2 H3 H4 H5 H6 H7. unfold WO. fsplit.
  - fall a. fintro Ha. fall b. fintro Hb. fintro Hab. fintro Hba.
    pose proof H7 as C. finst C a. fmp C Ha. finst C b. fmp C Hb. pose proof (iff_l _ _ _ C Hab) as S1. clear C.
    pose proof H7 as C. finst C b. fmp C Hb. finst C a. fmp C Ha. pose proof (iff_l _ _ _ C Hba) as S2. clear C.
    unfold SFR in S1, S2. fex S1 e1 S1'. fex S1' f1 S1. fdestr S1 S1a S1b. fdestr S1a Ra1 Rb1.
    fex S2 e2 S2'. fex S2' f2 S2. fdestr S2 S2a S2b. fdestr S2a Rb2 Ra2.
    pose proof H2 as U. finst U a. fmp U Ha. finst U e1 f2. fmp U Ra1. fmp U Ra2. rename U into Ea.
    pose proof H2 as U. finst U b. fmp U Hb. finst U f1 e2. fmp U Rb1. fmp U Rb2. rename U into Eb.
    pose proof H1 as U. finst U a. fmp U Ha. fex U e0 He0. fdestr He0 Oe0 Re0.
    pose proof H2 as U. finst U a. fmp U Ha. finst U e0 e1. fmp U Re0. fmp U Ra1. rename U into E01.
    fassert Oe1 : (Ord0 e1). { frew_in E01 (Ord0 $0) Oe0. exact Oe0. }
    fcases S1b S1c S1d; fcases S2b S2c S2d.
    + frew_in Eb ($0 ∈' f2`[↑]) S2c. frew_in Ea (f1`[↑] ∈' $0) S2c. exact (w_no_cycle2 HG HX _ _ S1c S2c).
    + fdestr S2d S2e S2f. frew_in Eb (e1`[↑] ∈' $0) S1c. frew_in S2e (e1`[↑] ∈' $0) S1c. frew_in Ea (e1`[↑] ∈' $0) S1c.
      exact (w_no_self HG HX _ S1c).
    + fdestr S1d S1e S1f. frew_in Ea (e2`[↑] ∈' $0) S2c. frew_in S1e (e2`[↑] ∈' $0) S2c. frew_in Eb (e2`[↑] ∈' $0) S2c.
      exact (w_no_self HG HX _ S2c).
    + fdestr S1d S1e S1f. fdestr S2d S2e S2f.
      fassert E21 : (e2 ≡' e1). { feq. }
      frew_in E21 (I5 Ow b`[↑] a`[↑] $0 P`[↑] Q`[↑]) S2f.
      frew_in E21 (I4 Rk b`[↑] $0 P`[↑] Q`[↑]) Rb2.
      finst H6 e1. fmp H6 Oe1. finst H6 a. fmp H6 Ha. finst H6 b. fmp H6 Hb. fmp H6 Ra1. fmp H6 Rb2. fmp H6 S1f.
      exact (IE H6 S2f).
  - fall T. fintro HT. fintro Hne.
    pose proof H3 as U. finst U T. fmp U HT. fmp U Hne. fex U e0 He0. fdestr He0 He0a Hmin. fdestr He0a Oe0 Hex.
    pose proof H4 as U. finst U T e0. fex U T0 HT0.
    fassert HT0r : (∀ ($0 ∈' T0`[↑] → $0 ∈' X`[↑] ∧ I4 Rk $0 e0`[↑] P`[↑] Q`[↑])).
    { fall z. fintro Hz. pose proof HT0 as H. finst H z. pose proof (iff_l _ _ _ H Hz) as Hz'. fdestr Hz' Hz1 Hz2.
      fsplit; [exact (wo_sub0_use HG _ _ _ HT Hz1)|exact Hz2]. }
    fassert HT0ne : (∃ ($0 ∈' T0`[↑])).
    { fex Hex z Hz. fdestr Hz Hz1 Hz2. fexists z. pose proof HT0 as H. finst H z. apply (iff_r _ _ _ H). fsplit; assumption. }
    pose proof H5 as U. finst U e0. fmp U Oe0. finst U T0. fmp U HT0r. fmp U HT0ne. fex U m Hm. fdestr Hm HmT0 Hm2.
    pose proof HT0 as H. finst H m. pose proof (iff_l _ _ _ H HmT0) as Hm'. clear H. fdestr Hm' HmT Rm.
    fexists m. unfold Lst. fsplit; [exact HmT|]. fall u. fintro Hu. fintro Hum.
    pose proof H7 as C. finst C m. fmp C (wo_sub0_use HG _ _ _ HT HmT). finst C u. fmp C (wo_sub0_use HG _ _ _ HT Hu).
    apply (iff_r _ _ _ C). clear C. unfold SFR.
    pose proof H1 as U. finst U u. fmp U (wo_sub0_use HG _ _ _ HT Hu). fex U eu Heu. fdestr Heu Oeu Ru.
    fexists e0. fexists eu. fsplit; [fsplit; assumption|].
    pose proof (w_ord_tri HG HX e0 eu Oe0 Oeu) as Tri. fcases Tri Tri1 Tri2; [fcases Tri1 Tri3 Tri4|].
    + fleft. exact Tri3.
    + fright. fsplit; [exact Tri4|]. frew_in Tri4 (I4 Rk u`[↑] $0 P`[↑] Q`[↑]) Ru.
      finst Hm2 u. fassert HuT0 : (u ∈' T0).
      { pose proof HT0 as H. finst H u. apply (iff_r _ _ _ H). fsplit; assumption. }
      fmp Hm2 HuT0. exact (IE Hm2 Hum).
    + fabsurd. finst Hmin eu. fmp Hmin Tri2. apply (IE Hmin). fexists u. fsplit; assumption.
Qed.

Lemma w_union0_unique {G} (HG : incl ZF0base G) (HX : WOx G) x u u' :
  G ⊢C Union0 x u -> G ⊢C Union0 x u' -> G ⊢C u ≡' u'.
Proof. wr @union0_unique. Qed.

(** ** Functionality of the operations *)
Lemma wo_dom0_unique {G} (HG : incl ZF0base G) (HX : WOx G) f d d' : G ⊢C Dom0 f d -> G ⊢C Dom0 f d' -> G ⊢C d ≡' d'.
Proof.
  intros H1 H2. apply (ext_rule HG); unfold sub'; fall x; fintro Hx.
  - fobtain (w_dom0_app HG HX f d x H1 Hx) as v Hv. exact (w_dom0_in HG HX f d' x v H2 Hv).
  - fobtain (w_dom0_app HG HX f d' x H2 Hx) as v Hv. exact (w_dom0_in HG HX f d x v H1 Hv).
Qed.

Lemma wo_ext0_fun {G} (HG : incl ZF0base G) (HX : WOx G) e v z z' : G ⊢C Ext0 e v z -> G ⊢C Ext0 e v z' -> G ⊢C z ≡' z'.
Proof.
  intros H1 H2. unfold Ext0 in H1, H2.
  fex H1 p Hp. fdestr Hp Hp1 Hp2. fex Hp2 x Hx. fdestr Hx Hx1 Hx2. fex Hx2 d Hd. fdestr Hd Hd1 Hd2.
  fdestr Hd2 Hd3 Hsub. fdestr Hd3 Hd4 Hall. fdestr Hd4 Hop Hdom.
  fex H2 p' Hp'. fdestr Hp' Hp1' Hp2'. fex Hp2' x' Hx'. fdestr Hx' Hx1' Hx2'. fex Hx2' d' Hd'. fdestr Hd' Hd1' Hd2'.
  fdestr Hd2' Hd3' Hsub'. fdestr Hd3' Hd4' Hall'. fdestr Hd4' Hop' Hdom'.
  pose proof (wo_dom0_unique HG HX e d d' Hdom Hdom') as Edd.
  frew_in Edd (OP0 $0 v`[↑] p'`[↑]) Hop'.
  pose proof (w_op0_unique HG HX _ _ _ _ Hop Hop') as Epp.
  apply (ext_rule HG); unfold sub'; fall w; fintro Hw.
  - finst Hall w. fmp Hall Hw. fcases Hall A1 A2.
    + exact (wo_sub0_use HG _ _ _ Hsub' A1).
    + fmem.
  - finst Hall' w. fmp Hall' Hw. fcases Hall' A1 A2.
    + exact (wo_sub0_use HG _ _ _ Hsub A1).
    + fmem.
Qed.

#[local] Ltac sepof_half H1 H2 :=
  let z := fresh "z" in let Hz := fresh "Hz" in
  let A := fresh "A" in let A1 := fresh "A" in let A2 := fresh "A" in let B := fresh "B" in
  unfold sub'; fall z; fintro Hz;
  pose proof (CE1 H1) as A; finst A z; fmp A Hz; fdestr A A1 A2;
  pose proof (CE2 H2) as B; finst B z; fmp B A1; exact (IE B A2).
#[local] Ltac sepof_tac H1 H2 :=
  let HG := getHG in
  unfold Op, SepOf in H1, H2; cbn in H1, H2;
  apply (ext_rule HG); [sepof_half H1 H2 | sepof_half H2 H1].

Lemma wo_op_fun {G} (HG : incl ZF0base G) (HX : WOx G) k a b c y y' :
  G ⊢C Op k a b c y -> G ⊢C Op k a b c y' -> G ⊢C y ≡' y'.
Proof.
  intros H1 H2. destruct k as [|[|[|[|[|[|[|[|k]]]]]]]].
  - unfold Op, Pair0 in H1, H2. apply (ext_rule HG); unfold sub'; fall z; fintro Hz.
    + pose proof (CE2 H1) as A. finst A z. fmp A Hz. pose proof (CE1 H2) as B2. fdestr B2 B3 B4.
      fcases A A1 A2; fmem.
    + pose proof (CE2 H2) as A. finst A z. fmp A Hz. pose proof (CE1 H1) as B2. fdestr B2 B3 B4.
      fcases A A1 A2; fmem.
  - unfold Op in H1, H2. exact (w_union0_unique HG HX _ _ _ H1 H2).
  - sepof_tac H1 H2.
  - unfold Op in H1, H2. apply (ext_rule HG); unfold sub'; fall z; fintro Hz.
    + pose proof (CE1 H1) as A. finst A z. fmp A Hz. fex A e He. fdestr He He1 He2. fex He2 v Hv. fdestr Hv Hv1 Hv2.
      pose proof (CE2 H2) as B. finst B e. fmp B He1. finst B v. fmp B Hv1. fex B z' Hz'. fdestr Hz' Hz1 Hz2.
      pose proof (wo_ext0_fun HG HX e v z z' Hv2 Hz2) as E. fmem.
    + pose proof (CE1 H2) as A. finst A z. fmp A Hz. fex A e He. fdestr He He1 He2. fex He2 v Hv. fdestr Hv Hv1 Hv2.
      pose proof (CE2 H1) as B. finst B e. fmp B He1. finst B v. fmp B Hv1. fex B z' Hz'. fdestr Hz' Hz1 Hz2.
      pose proof (wo_ext0_fun HG HX e v z z' Hv2 Hz2) as E. fmem.
  - sepof_tac H1 H2.
  - sepof_tac H1 H2.
  - sepof_tac H1 H2.
  - sepof_tac H1 H2.
  - unfold Op in H1. cbn in H1. apply Exp. exact H1.
Qed.

(** ** Kinds *)
Lemma wo_nimp {G} (A : form) : G ⊢C (A → ⊥) -> G ⊢C A -> G ⊢C ⊥.
Proof. intros H1 H2. exact (IE H1 H2). Qed.

Lemma NB_lt {G} j k B t : j < k -> G ⊢C NB k B t -> G ⊢C ¬ (HasK j B t).
Proof.
  revert j. induction k as [|k IH]; intros j Hjk H; [lia|]. rewrite NB_S in H.
  destruct (Nat.eq_dec j k) as [->|Hne]; [exact (CE2 H)|]. apply IH; [lia|exact (CE1 H)].
Qed.

Lemma neword_intro {G} j K B W t t' : j < K -> G ⊢C Clause j B W t t' -> G ⊢C NewOrd K B W t t'.
Proof.
  induction K as [|K IH]; intros Hj H; [lia|]. rewrite NewOrd_S.
  destruct (Nat.eq_dec j K) as [->|Hne]; [apply DI2; exact H|apply DI1; apply IH; [lia|exact H]].
Qed.

Lemma hask_intro {G} k B a b c t : G ⊢C a ∈' B -> G ⊢C b ∈' B -> G ⊢C c ∈' B -> G ⊢C Op k a b c t -> G ⊢C HasK k B t.
Proof.
  intros Ha Hb Hc H. unfold HasK. fexists a. fsplit; [exact Ha|]. fexists b. fsplit; [exact Hb|].
  fexists c. fsplit; [exact Hc|]. exact H.
Qed.

(** every new element of Step(B) has a kind *)
Lemma new_kind {G} (HG : incl ZF0base G) B B' t : G ⊢C Step B B' -> G ⊢C t ∈' B' -> G ⊢C ¬ (t ∈' B) ->
  G ⊢C NB 8 B t -> G ⊢C ⊥.
Proof.
  intros HS Ht Hn HNB. unfold Step in HS. fdestr HS HS1 HS2. fdestr HS1 HS3 HS4.
  finst HS4 t. fmp HS4 Ht. fcases HS4 A1 A2; [fneg|].
  fex A2 a Ha. fdestr Ha Ha1 Ha2. fex Ha2 b Hb. fdestr Hb Hb1 Hb2. fex Hb2 c Hc. fdestr Hc Hc1 Hc2.
  unfold Ops in Hc2.
  repeat match goal with H : _ ⊢C (_ ∨ _) |- _ => let H1 := fresh "O" in let H2 := fresh "O" in fcases H H1 H2 end;
  match goal with H : _ ⊢C Op ?k _ _ _ _ |- _ =>
    exact (wo_nimp _ (NB_lt k 8 B t ltac:(lia) HNB) (hask_intro k B a b c t Ha1 Hb1 Hc1 H)) end.
Qed.

(** ** Asymmetry of the code order *)
Lemma wo_irr {G} W X a : G ⊢C WO W X -> G ⊢C a ∈' X -> G ⊢C App0 W a a -> G ⊢C ⊥.
Proof. intros H Ha H1. exact (wo_asym W X a a H Ha Ha H1 H1). Qed.

Lemma lex3_asym {G} (HG : incl ZF0base G) W B a b c a' b' c' : G ⊢C WO W B ->
  G ⊢C a ∈' B -> G ⊢C b ∈' B -> G ⊢C c ∈' B -> G ⊢C a' ∈' B -> G ⊢C b' ∈' B -> G ⊢C c' ∈' B ->
  G ⊢C Lex3 W a b c a' b' c' -> G ⊢C Lex3 W a' b' c' a b c -> G ⊢C ⊥.
Proof.
  intros HW Ha Hb Hc Ha' Hb' Hc' H1 H2. unfold Lex3 in H1, H2.
  fcases H1 L1 L2; fcases H2 R1 R2.
  - exact (wo_asym W B a a' HW Ha Ha' L1 R1).
  - fdestr R2 R3 R4. frew_in R3 (App0 W`[↑] a`[↑] $0) L1. exact (wo_irr W B a HW Ha L1).
  - fdestr L2 L3 L4. frew_in L3 (App0 W`[↑] a'`[↑] $0) R1. exact (wo_irr W B a' HW Ha' R1).
  - fdestr L2 L3 L4. fdestr R2 R3 R4. fcases L4 L5 L6; fcases R4 R5 R6.
    + exact (wo_asym W B b b' HW Hb Hb' L5 R5).
    + fdestr R6 R7 R8. frew_in R7 (App0 W`[↑] b`[↑] $0) L5. exact (wo_irr W B b HW Hb L5).
    + fdestr L6 L7 L8. frew_in L7 (App0 W`[↑] b'`[↑] $0) R5. exact (wo_irr W B b' HW Hb' R5).
    + fdestr L6 L7 L8. fdestr R6 R7 R8. exact (wo_asym W B c c' HW Hc Hc' L8 R8).
Qed.

Lemma cok_asym {G} (HG : incl ZF0base G) k B W t t' : G ⊢C WO W B ->
  G ⊢C COk k B W t t' -> G ⊢C COk k B W t' t -> G ⊢C ⊥.
Proof.
  intros HW H1 H2. unfold COk in H1, H2.
  fex H1 a Ha. fdestr Ha Ha1 Ha2. fex Ha2 b Hb. fdestr Hb Hb1 Hb2. fex Hb2 c Hc. fdestr Hc Hc1 Hc2. fdestr Hc2 Hop1 Hall1.
  fex H2 a' Ha'. fdestr Ha' Ha1' Ha2'. fex Ha2' b' Hb'. fdestr Hb' Hb1' Hb2'. fex Hb2' c' Hc'. fdestr Hc' Hc1' Hc2'.
  fdestr Hc2' Hop2 Hall2.
  finst Hall1 a'. fmp Hall1 Ha1'. finst Hall1 b'. fmp Hall1 Hb1'. finst Hall1 c'. fmp Hall1 Hc1'. fmp Hall1 Hop2.
  finst Hall2 a. fmp Hall2 Ha1. finst Hall2 b. fmp Hall2 Hb1. finst Hall2 c. fmp Hall2 Hc1. fmp Hall2 Hop1.
  exact (lex3_asym HG W B a b c a' b' c' HW Ha1 Hb1 Hc1 Ha1' Hb1' Hc1' Hall1 Hall2).
Qed.

Lemma clause_asym {G} (HG : incl ZF0base G) B W j j' t t' : G ⊢C WO W B ->
  G ⊢C Clause j B W t t' -> G ⊢C Clause j' B W t' t -> G ⊢C ⊥.
Proof.
  intros HW H1 H2. unfold Clause in H1, H2. fdestr H1 H1a H1b. fdestr H1a Hk1 NB1. fdestr H1b NB1' C1.
  fdestr H2 H2a H2b. fdestr H2a Hk2 NB2. fdestr H2b NB2' C2.
  destruct (lt_eq_lt_dec j j') as [[Hlt| <-]|Hlt].
  - exact (wo_nimp _ (NB_lt j j' B t Hlt NB2') Hk1).
  - fcases C1 C1a C1b; [fneg|]. fcases C2 C2a C2b; [fneg|]. exact (cok_asym HG j B W t t' HW C1b C2b).
  - exact (wo_nimp _ (NB_lt j' j B t' Hlt NB1') Hk2).
Qed.

Lemma clause_neword {G} (HG : incl ZF0base G) B W j t t' K : G ⊢C WO W B ->
  G ⊢C Clause j B W t t' -> G ⊢C NewOrd K B W t' t -> G ⊢C ⊥.
Proof.
  revert G HG. induction K as [|K IH]; intros G HG HW H1 H2; [exact H2|].
  rewrite NewOrd_S in H2. fcases H2 H3 H4.
  - exact (IH _ HG HW H1 H3).
  - exact (clause_asym HG B W j K t t' HW H1 H4).
Qed.

Lemma neword_asym {G} (HG : incl ZF0base G) B W t t' K K' : G ⊢C WO W B ->
  G ⊢C NewOrd K B W t t' -> G ⊢C NewOrd K' B W t' t -> G ⊢C ⊥.
Proof.
  revert G HG. induction K as [|K IH]; intros G HG HW H1 H2; [exact H1|].
  rewrite NewOrd_S in H1. fcases H1 H3 H4.
  - exact (IH _ HG HW H3 H2).
  - exact (clause_neword HG B W K t t' K' HW H4 H2).
Qed.

(** ** Least elements for the code order *)
Lemma fb_A1P k : fb 3 (A1P k $0 $1 $2).
Proof. destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; fbcomp. Qed.
Lemma fb_A2P k : fb 4 (A2P k $0 $1 $2 $3).
Proof. destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; fbcomp. Qed.
Lemma fb_A3P k : fb 4 (A3P k $0 $1 $2 $3).
Proof. destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; fbcomp. Qed.

Lemma in_code {G} (HX : WOx G) k : k < 8 ->
  In (forall_times 2 (ax_sep' (A1P k $0 $1 $2))) G /\ In (forall_times 3 (ax_sep' (A2P k $0 $1 $2 $3))) G /\
  In (forall_times 3 (ax_sep' (A3P k $0 $1 $2 $3))) G.
Proof.
  intros Hk. assert (H : forall a, In a code_insts -> In a G).
  { intros a Ha. apply (in_wo HX). unfold wo_list. rewrite !in_app_iff. tauto. }
  repeat split; apply H; unfold code_insts; apply in_flat_map; exists k; (split; [apply in_seq; lia|cbn; tauto]).
Qed.

(** the least new element w.r.t. the code order, when kind k is the least kind present in T *)
Lemma code_min {G} (HG : incl ZF0base G) (HX : WOx G) k B W T : k < 8 -> G ⊢C WO W B ->
  G ⊢C ∀ ($0 ∈' T`[↑] → NB k B`[↑] $0) -> G ⊢C ∃ ($0 ∈' T`[↑] ∧ HasK k B`[↑] $0) ->
  G ⊢C ∃ ($0 ∈' T`[↑] ∧ ∀ ($0 ∈' T`[↑]`[↑] → ¬ ($0 ≡' $1) → NewOrd 8 B`[↑]`[↑] W`[↑]`[↑] $1 $0)).
Proof.
  intros Hk HW HNB Hex. destruct (in_code HX k Hk) as (I1 & I2 & I3).
  fex Hex t Ht. fdestr Ht Ht1 Ht2. unfold HasK in Ht2.
  fex Ht2 a Ha. fdestr Ha Ha1 Ha2. fex Ha2 b Hb. fdestr Hb Hb1 Hb2. fex Hb2 c Hc. fdestr Hc Hc1 Hc2.
  (* A1 *)
  pose proof (sep_use _ 2 (A1P k $0 $1 $2) (T .: B .: var) B I1 (fb_A1P k)) as S1. simp_in S1. fex S1 A1 HA1.
  fassert HA1B : (Sub0 A1 B). { unfold Sub0. fall z. fintro Hz. pose proof HA1 as H. finst H z. exact (CE1 (iff_l _ _ _ H Hz)). }
  fassert Ha_A1 : (a ∈' A1).
  { pose proof HA1 as H. finst H a. apply (iff_r _ _ _ H). fsplit; [exact Ha1|]. unfold A1P. fexists t. fsplit; [exact Ht1|].
    fexists b. fsplit; [exact Hb1|]. fexists c. fsplit; [exact Hc1|]. exact Hc2. }
  pose proof (wo_least W B A1 a HW HA1B Ha_A1) as T1. fex T1 a0 Ha0.
  pose proof HA1 as H. finst H a0. pose proof (iff_l _ _ _ H (lst_in _ _ _ Ha0)) as Ha0'. clear H. fdestr Ha0' Ha0B Ha0P.
  unfold A1P in Ha0P. fex Ha0P t1 Ht1'. fdestr Ht1' Ht1a Ht1b. fex Ht1b b1 Hb1'. fdestr Hb1' Hb1a Hb1b.
  fex Hb1b c1 Hc1'. fdestr Hc1' Hc1a Hc1b.
  (* A2 *)
  pose proof (sep_use _ 3 (A2P k $0 $1 $2 $3) (T .: B .: a0 .: var) B I2 (fb_A2P k)) as S2. simp_in S2. fex S2 A2 HA2.
  fassert HA2B : (Sub0 A2 B). { unfold Sub0. fall z. fintro Hz. pose proof HA2 as H. finst H z. exact (CE1 (iff_l _ _ _ H Hz)). }
  fassert Hb_A2 : (b1 ∈' A2).
  { pose proof HA2 as H. finst H b1. apply (iff_r _ _ _ H). fsplit; [exact Hb1a|]. unfold A2P. fexists t1. fsplit; [exact Ht1a|].
    fexists c1. fsplit; [exact Hc1a|]. exact Hc1b. }
  pose proof (wo_least W B A2 b1 HW HA2B Hb_A2) as T2. fex T2 b0 Hb0.
  pose proof HA2 as H. finst H b0. pose proof (iff_l _ _ _ H (lst_in _ _ _ Hb0)) as Hb0'. clear H. fdestr Hb0' Hb0B Hb0P.
  unfold A2P in Hb0P. fex Hb0P t2 Ht2'. fdestr Ht2' Ht2a Ht2b. fex Ht2b c2 Hc2'. fdestr Hc2' Hc2a Hc2b.
  (* A3 *)
  pose proof (sep_use _ 3 (A3P k $0 $1 $2 $3) (T .: a0 .: b0 .: var) B I3 (fb_A3P k)) as S3. simp_in S3. fex S3 A3 HA3.
  fassert HA3B : (Sub0 A3 B). { unfold Sub0. fall z. fintro Hz. pose proof HA3 as H. finst H z. exact (CE1 (iff_l _ _ _ H Hz)). }
  fassert Hc_A3 : (c2 ∈' A3).
  { pose proof HA3 as H. finst H c2. apply (iff_r _ _ _ H). fsplit; [exact Hc2a|]. unfold A3P. fexists t2.
    fsplit; [exact Ht2a|]. exact Hc2b. }
  pose proof (wo_least W B A3 c2 HW HA3B Hc_A3) as T3. fex T3 c0 Hc0.
  pose proof HA3 as H. finst H c0. pose proof (iff_l _ _ _ H (lst_in _ _ _ Hc0)) as Hc0'. clear H. fdestr Hc0' Hc0B Hc0P.
  unfold A3P in Hc0P. fex Hc0P t0 Ht0. fdestr Ht0 Ht0a Ht0b.
  (* t0 is least *)
  fexists t0. fsplit; [exact Ht0a|]. fall u. fintro Hu. fintro Hut0.
  apply (neword_intro k 8 B W t0 u Hk). unfold Clause. fsplit; fsplit.
  - exact (hask_intro k B a0 b0 c0 t0 Ha0B Hb0B Hc0B Ht0b).
  - pose proof HNB as H. finst H t0. exact (IE H Ht0a).
  - pose proof HNB as H. finst H u. exact (IE H Hu).
  - apply (XM_rule _ (HasK k B u)); [|fintro Hn; fleft; exact Hn].
    fintro Hku. fright. unfold COk. fexists a0. fsplit; [exact Ha0B|]. fexists b0. fsplit; [exact Hb0B|].
    fexists c0. fsplit; [exact Hc0B|]. fsplit; [exact Ht0b|].
    fall a'. fintro Ha'. fall b'. fintro Hb'. fall c'. fintro Hc'. fintro Hop.
    unfold Lex3. apply (XM_rule _ (a' ≡' a0)); swap 1 2.
    { fintro Na. fleft. apply (lst_lt W A1 a0 a' Ha0); [|exact Na].
      pose proof HA1 as H. finst H a'. apply (iff_r _ _ _ H). fsplit; [exact Ha'|]. unfold A1P. fexists u. fsplit; [exact Hu|].
      fexists b'. fsplit; [exact Hb'|]. fexists c'. fsplit; [exact Hc'|]. exact Hop. }
    fintro Ea. fright. fsplit; [feq|]. frew_in Ea (Op k $0 b'`[↑] c'`[↑] u`[↑]) Hop.
    apply (XM_rule _ (b' ≡' b0)); swap 1 2.
    { fintro Nb. fleft. apply (lst_lt W A2 b0 b' Hb0); [|exact Nb].
      pose proof HA2 as H. finst H b'. apply (iff_r _ _ _ H). fsplit; [exact Hb'|]. unfold A2P. fexists u. fsplit; [exact Hu|].
      fexists c'. fsplit; [exact Hc'|]. exact Hop. }
    fintro Eb. fright. fsplit; [feq|]. frew_in Eb (Op k a0`[↑] $0 c'`[↑] u`[↑]) Hop.
    apply (XM_rule _ (c' ≡' c0)); swap 1 2.
    { fintro Nc. apply (lst_lt W A3 c0 c' Hc0); [|exact Nc].
      pose proof HA3 as H. finst H c'. apply (iff_r _ _ _ H). fsplit; [exact Hc'|]. unfold A3P. fexists u. fsplit; [exact Hu|].
      exact Hop. }
    fintro Ec. frew_in Ec (Op k a0`[↑] b0`[↑] $0 u`[↑]) Hop. fabsurd. apply (IE Hut0).
    exact (wo_op_fun HG HX k a0 b0 c0 u t0 Hop Ht0b).
Qed.

(** search for the least kind present in T *)
Lemma code_search n : forall K {G} (HG : incl ZF0base G) (HX : WOx G) B B' W T, K + n = 8 -> G ⊢C WO W B ->
  G ⊢C Step B B' -> G ⊢C Sub0 T B' -> G ⊢C ∀ ($0 ∈' T`[↑] → ¬ ($0 ∈' B`[↑])) -> G ⊢C ∃ ($0 ∈' T`[↑]) ->
  G ⊢C ∀ ($0 ∈' T`[↑] → NB K B`[↑] $0) ->
  G ⊢C ∃ ($0 ∈' T`[↑] ∧ ∀ ($0 ∈' T`[↑]`[↑] → ¬ ($0 ≡' $1) → NewOrd 8 B`[↑]`[↑] W`[↑]`[↑] $1 $0)).
Proof.
  induction n as [|n IH]; intros K G HG HX B B' W T HKn HW HS HT Hnew Hne HNB.
  - replace K with 8 in HNB by lia. fabsurd. fex Hne t Ht.
    pose proof Hnew as H. finst H t. fmp H Ht. pose proof HNB as H'. finst H' t. fmp H' Ht.
    exact (new_kind HG B B' t HS (wo_sub0_use HG _ _ _ HT Ht) H H').
  - apply (XM_rule _ (∃ ($0 ∈' T`[↑] ∧ HasK K B`[↑] $0))).
    + fintro Hex. exact (code_min HG HX K B W T ltac:(lia) HW HNB Hex).
    + fintro Hno. apply (IH (S K) _ HG HX B B' W T ltac:(lia) HW HS HT Hnew Hne).
      fall t. fintro Ht. rewrite NB_S. fsplit.
      * pose proof HNB as H. finst H t. exact (IE H Ht).
      * fintro Hk. apply (IE Hno). fexists t. fsplit; assumption.
Qed.

(** the new part of Step(B) is well-ordered by the code order (in the form needed by [sum_wo]) *)
Lemma new_wo_least {G} (HG : incl ZF0base G) (HX : WOx G) B B' W : G ⊢C WO W B -> G ⊢C Step B B' ->
  G ⊢C ∀ (Sub0 $0 B'`[↑] → (∀ ($0 ∈' $1 → ¬ ($0 ∈' B`[↑]`[↑]))) → (∃ ($0 ∈' $1)) →
          ∃ ($0 ∈' $1 ∧ ∀ ($0 ∈' $2 → ¬ ($0 ≡' $1) → I4 NOf $1 $0 B`[↑]`[↑]`[↑] W`[↑]`[↑]`[↑]))).
Proof.
  intros HW HS. fall T. fintro HT. fintro Hnew. fintro Hne. unfold I4, NOf. simp.
  apply (code_search 8 0 HG HX B B' W T eq_refl HW HS HT Hnew Hne).
  fall t. fintro Ht. unfold NB. cbn. apply II. apply Ctx. now left.
Qed.

Lemma new_wo_asym {G} (HG : incl ZF0base G) B B' W : G ⊢C WO W B ->
  G ⊢C ∀ ($0 ∈' B'`[↑] → ∀ ($0 ∈' B'`[↑]`[↑] → ¬ ($1 ∈' B`[↑]`[↑]) → ¬ ($0 ∈' B`[↑]`[↑]) →
          I4 NOf $1 $0 B`[↑]`[↑] W`[↑]`[↑] → I4 NOf $0 $1 B`[↑]`[↑] W`[↑]`[↑] → ⊥)).
Proof.
  intros HW. fall a. fintro Ha. fall b. fintro Hb. fintro Na. fintro Nb. fintro H1. fintro H2.
  unfold I4, NOf in H1, H2. simp_in H1. simp_in H2. exact (neword_asym HG B W a b 8 8 HW H1 H2).
Qed.

#[local] Ltac inwo1 := match goal with HX : WOx _ |- In _ _ =>
  apply (in_wo HX); unfold wo_list, wo_insts1; rewrite ?in_app_iff;
  cbn -[forall_times ax_sep' rec_insts code_insts]; right; right; left; repeat (first [left; reflexivity | right]) end.
#[local] Ltac getinst X T := match goal with |- ?G' ⊢C _ => assert (X : In T G') by inwo1 end.

(** ** Ordinal and set helpers *)
Lemma wo_succ_in {G} x s : G ⊢C Succ0 x s -> G ⊢C x ∈' s.
Proof. intros H. exact (CE1 (CE1 H)). Qed.
Lemma wo_succ_sub {G} x s : G ⊢C Succ0 x s -> G ⊢C Sub0 x s.
Proof. intros H. exact (CE2 (CE1 H)). Qed.
Lemma wo_succ_el {G} x s z : G ⊢C Succ0 x s -> G ⊢C z ∈' s -> G ⊢C z ∈' x ∨ z ≡' x.
Proof. intros H Hz. pose proof (CE2 H) as H2. finst H2 z. exact (IE H2 Hz). Qed.
Lemma wo_emp_el {G} e z : G ⊢C Emp0 e -> G ⊢C z ∈' e -> G ⊢C ⊥.
Proof. intros H Hz. unfold Emp0 in H. finst H z. exact (IE H Hz). Qed.

Lemma wo_emp_unique {G} (HG : incl ZF0base G) e e' : G ⊢C Emp0 e -> G ⊢C Emp0 e' -> G ⊢C e ≡' e'.
Proof.
  intros H1 H2. apply (ext_rule HG); unfold sub'; fall z; fintro Hz; fabsurd.
  - exact (wo_emp_el e z H1 Hz).
  - exact (wo_emp_el e' z H2 Hz).
Qed.

Lemma wo_succ_inj {G} (HG : incl ZF0base G) (HX : WOx G) x x' s : G ⊢C Succ0 x s -> G ⊢C Succ0 x' s -> G ⊢C x ≡' x'.
Proof.
  intros H1 H2. pose proof (wo_succ_el x' s x H2 (wo_succ_in x s H1)) as A. pose proof (wo_succ_el x s x' H1 (wo_succ_in x' s H2)) as B.
  fcases A A1 A2; [|exact A2]. fabsurd. fcases B B1 B2.
  - exact (w_no_cycle2 HG HX x x' A1 B1).
  - frew_in B2 (x`[↑] ∈' $0) A1. exact (w_no_self HG HX x A1).
Qed.

Lemma wo_lim_not_succ {G} (HG : incl ZF0base G) (HX : WOx G) l m : G ⊢C Lim0 l -> G ⊢C Succ0 m l -> G ⊢C ⊥.
Proof.
  intros HL HS. unfold Lim0 in HL. pose proof (CE2 HL) as H. finst H m. fmp H (wo_succ_in m l HS).
  fex H y Hy. fdestr Hy Hy1 Hy2. pose proof (wo_succ_el m l y HS Hy1) as A. fcases A A1 A2.
  - exact (w_no_cycle2 HG HX m y Hy2 A1).
  - frew_in A2 (m`[↑] ∈' $0) Hy2. exact (w_no_self HG HX m Hy2).
Qed.

Lemma wo_lim_ne {G} l : G ⊢C Lim0 l -> G ⊢C Emp0 l -> G ⊢C ⊥.
Proof.
  intros HL HE. unfold Lim0 in HL. pose proof (CE2 (CE1 HL)) as H. fex H y Hy. fdestr Hy Hy1 Hy2.
  exact (wo_emp_el l y HE Hy1).
Qed.

(** ** The step formula [Sin] *)
Lemma Sin_eq f xi v p : SR Sin f xi v p =
  ((Emp0 xi → v ≡' p) ∧ (∀ ($0 ∈' xi`[↑] → Succ0 $0 xi`[↑] → ∃ (App0 f`[↑]`[↑] $1 $0 ∧ NextP $0 v`[↑]`[↑])))) ∧
  (Lim0 xi → Emp0 v).
Proof. unfold SR, Sin. simp. reflexivity. Qed.

Lemma Scl_eq g xi v p : SR Scl g xi v p =
  ((Emp0 xi → v ≡' p) ∧ (∀ ($0 ∈' xi`[↑] → Succ0 $0 xi`[↑] → ∃ (App0 g`[↑]`[↑] $1 $0 ∧ Step $0 v`[↑]`[↑])))) ∧
  (Lim0 xi → Emp0 v).
Proof. unfold SR, Scl. simp. reflexivity. Qed.

Lemma fb_phNext : fb 4 phNext.  Proof. fbcomp. Qed.
Lemma fb_Sin : fb 4 Sin.  Proof. fbcomp. Qed.

Lemma nextp_ex {G} (HG : incl ZF0base G) (HX : WOx G) u : G ⊢C ∃ NextP u`[↑] $0.
Proof.
  apply (XM_rule _ (∃ (∃ (OP0 $1 $0 u`[↑]`[↑])))).
  - fintro H. fex H B HB. fex HB W HW.
    fobtain (w_step_ex HG HX B) as B' HB'.
    getinst Hin1 (forall_times 3 (ax_sep' (PSF phNext))). pose proof (pairset_ex HG 2 phNext (B .: W .: var) B' fb_phNext Hin1) as T. unfold phNext in T. simp_in T. fex T W' HW'.
    fobtain (w_op0_ex HG HX B' W') as v Hv.
    fexists v. unfold NextP. fleft. fexists B. fexists W. fsplit; [exact HW|]. fexists B'. fexists W'. fsplit; [exact Hv|].
    unfold NxR. fsplit; [exact HB'|exact HW'].
  - fintro H. fobtain (w_emp0_ex HG HX) as e He. fexists e. unfold NextP. fright. fsplit; [|exact He].
    fall B. fall W. fintro HO. apply (IE H). fexists B. fexists W. exact HO.
Qed.

Lemma nextp_unique {G} (HG : incl ZF0base G) (HX : WOx G) u v v' : G ⊢C NextP u v -> G ⊢C NextP u v' -> G ⊢C v ≡' v'.
Proof.
  intros H1 H2. unfold NextP in H1, H2. fcases H1 A1 A2; fcases H2 B1 B2.
  - fex A1 b Hb. fex Hb w Hw. fdestr Hw Hw1 Hw2. fex Hw2 b' Hb'. fex Hb' w' Hw'. fdestr Hw' Hw3 Hw4.
    fex B1 c Hc. fex Hc x Hx. fdestr Hx Hx1 Hx2. fex Hx2 c' Hc'. fex Hc' x' Hx'. fdestr Hx' Hx3 Hx4.
    pose proof (w_op0_inj HG HX _ _ _ _ _ Hw1 Hx1) as E. fdestr E E1 E2.
    frew_in E1 (NxR $0 x`[↑] c'`[↑] x'`[↑]) Hx4. frew_in E2 (NxR b`[↑] $0 c'`[↑] x'`[↑]) Hx4.
    unfold NxR in Hw4, Hx4. fdestr Hw4 S1 P1. fdestr Hx4 S2 P2.
    pose proof (w_step_unique HG HX _ _ _ S1 S2) as E3.
    frew_in E3 (PairSet $0 x'`[↑] (SumR b`[↑]`[↑]`[↑] w`[↑]`[↑]`[↑] (I4 NOf $1 $0 b`[↑]`[↑]`[↑] w`[↑]`[↑]`[↑]) $1 $0)) P2.
    pose proof (pairset_unique HG _ _ _ _ P1 P2) as E4.
    frew_in E3 (OP0 $0 x'`[↑] v'`[↑]) Hx3. frew_in E4 (OP0 b'`[↑] $0 v'`[↑]) Hx3.
    exact (w_op0_unique HG HX _ _ _ _ Hw3 Hx3).
  - fex A1 b Hb. fex Hb w Hw. fdestr Hw Hw1 Hw2. fdestr B2 B3 B4. finst B3 b w. fabsurd. exact (IE B3 Hw1).
  - fex B1 b Hb. fex Hb w Hw. fdestr Hw Hw1 Hw2. fdestr A2 A3 A4. finst A3 b w. fabsurd. exact (IE A3 Hw1).
  - exact (wo_emp_unique HG v v' (CE2 A2) (CE2 B2)).
Qed.

Lemma Sin_loc {G} (HG : incl ZF0base G) (HX : WOx G) p : G ⊢C SLoc Sin p.
Proof.
  unfold SLoc. fall f. fall f'. fall xi. fall v. fintro Hf. fintro Hf'. fintro Hxi. fintro HA. fintro H.
  rewrite Sin_eq in H |- *. fdestr H H12 H3. fdestr H12 H1 H2. fsplit; [fsplit|exact H3]; [exact H1|].
  fall m. fintro Hm. fintro Hs. finst H2 m. fmp H2 Hm. fmp H2 Hs. fex H2 u Hu. fdestr Hu Hu1 Hu2.
  fexists u. fsplit; [|exact Hu2]. unfold Agree in HA. finst HA m. fmp HA Hm. finst HA u. exact (iff_l _ _ _ HA Hu1).
Qed.

Lemma Sin_tot {G} (HG : incl ZF0base G) (HX : WOx G) p : G ⊢C STot Sin p.
Proof.
  unfold STot. fall f. fall xi. fintro Hf. fintro Hxi. fintro Hval.
  pose proof (w_ord_cases HG HX xi Hxi) as C. fcases C C1 C2; [fcases C1 C3 C4|].
  - fexists p. rewrite Sin_eq. fsplit; [fsplit|].
    + fintro Hdum. apply (eq_refl' HG).
    + fall m. fintro Hm. fabsurd. exact (wo_emp_el xi m C3 Hm).
    + fintro HL. fabsurd. exact (wo_lim_ne xi HL C3).
  - fex C4 m Hm. fdestr Hm Hm1 Hm2. pose proof Hval as H. finst H m. fmp H (wo_succ_in m xi Hm2). fex H u Hu.
    fobtain (nextp_ex HG HX u) as v Hv. fexists v. rewrite Sin_eq. fsplit; [fsplit|].
    + fintro HE. fabsurd. exact (wo_emp_el xi m HE (wo_succ_in m xi Hm2)).
    + fall m'. fintro Hm'. fintro Hs'. pose proof (wo_succ_inj HG HX m m' xi Hm2 Hs') as E.
      fexists u. fsplit; [|exact Hv]. frew_in E (App0 f`[↑] $0 u`[↑]) Hu. exact Hu.
    + fintro HL. fabsurd. exact (wo_lim_not_succ HG HX xi m HL Hm2).
  - fobtain (w_emp0_ex HG HX) as e He. fexists e. rewrite Sin_eq. fsplit; [fsplit|].
    + fintro HE. fabsurd. exact (wo_lim_ne xi C2 HE).
    + fall m. fintro Hm. fintro Hs. fabsurd. exact (wo_lim_not_succ HG HX xi m C2 Hs).
    + fintro Hdum. exact He.
Qed.

Lemma Sin_fun {G} (HG : incl ZF0base G) (HX : WOx G) p : G ⊢C SFun Sin p.
Proof.
  unfold SFun. fall f. fall xi. fall v. fall v'. fintro Hf. fintro Hxi. fintro H1. fintro H2.
  rewrite Sin_eq in H1, H2. fdestr H1 H1a H1c. fdestr H1a H1x H1b. fdestr H2 H2a H2c. fdestr H2a H2x H2b.
  pose proof (w_ord_cases HG HX xi Hxi) as C. fcases C C1 C2; [fcases C1 C3 C4|].
  - fmp H1x C3. fmp H2x C3. feq.
  - fex C4 m Hm. fdestr Hm Hm1 Hm2.
    finst H1b m. fmp H1b (wo_succ_in m xi Hm2). fmp H1b Hm2. fex H1b u Hu. fdestr Hu Hu1 Hu2.
    finst H2b m. fmp H2b (wo_succ_in m xi Hm2). fmp H2b Hm2. fex H2b u' Hu'. fdestr Hu' Hu1' Hu2'.
    pose proof (w_fun0_app HG HX f m u u' Hf Hu1 Hu1') as E. frew_in E (NextP $0 v'`[↑]) Hu2'.
    exact (nextp_unique HG HX u v v' Hu2 Hu2').
  - fmp H1c C2. fmp H2c C2. exact (wo_emp_unique HG v v' H1c H2c).
Qed.

(** ** Functions with the same domain and values are equal *)
Lemma wo_fun_ext {G} (HG : incl ZF0base G) (HX : WOx G) h h' w : G ⊢C Fun0 h -> G ⊢C Fun0 h' -> G ⊢C Dom0 h w -> G ⊢C Dom0 h' w ->
  G ⊢C ∀ ($0 ∈' w`[↑] → ∀ (∀ (App0 h`[↑]`[↑]`[↑] $2 $1 → App0 h'`[↑]`[↑]`[↑] $2 $0 → $1 ≡' $0))) -> G ⊢C h ≡' h'.
Proof.
  intros Hf Hf' Hd Hd' Hag. apply (ext_rule HG); unfold sub'; fall p; fintro Hp.
  - pose proof (w_isrel0_el HG HX h p (CE1 Hf) Hp) as T. fex T a Ha. fex Ha b Hb.
    pose proof (w_app0_intro HG HX h a b p Hb Hp) as A.
    pose proof (w_dom0_in HG HX h w a b Hd A) as Aw.
    fobtain (w_dom0_app HG HX h' w a Hd' Aw) as b' Hb'.
    pose proof Hag as H. finst H a. fmp H Aw. finst H b b'. fmp H A. fmp H Hb'.
    unfold App0 in Hb'. fex Hb' p' Hp'. fdestr Hp' Hp1 Hp2.
    frew_in H (OP0 a`[↑] $0 p'`[↑]) Hp2.
    pose proof (w_op0_unique HG HX _ _ _ _ Hp2 Hb) as E. fmem.
  - pose proof (w_isrel0_el HG HX h' p (CE1 Hf') Hp) as T. fex T a Ha. fex Ha b Hb.
    pose proof (w_app0_intro HG HX h' a b p Hb Hp) as A.
    pose proof (w_dom0_in HG HX h' w a b Hd' A) as Aw.
    fobtain (w_dom0_app HG HX h w a Hd Aw) as b' Hb'.
    pose proof Hag as H. finst H a. fmp H Aw. finst H b' b. fmp H Hb'. fmp H A.
    unfold App0 in Hb'. fex Hb' p' Hp'. fdestr Hp' Hp1 Hp2.
    frew_in H (OP0 a`[↑] $0 p'`[↑]) Hp2.
    pose proof (w_op0_unique HG HX _ _ _ _ Hp2 Hb) as E. fmem.
Qed.

Lemma in_rec_Sin {G} (HX : WOx G) : incl (rec_insts Sin) G.
Proof. intros a Ha. apply (in_wo HX). unfold wo_list. rewrite !in_app_iff. tauto. Qed.

Lemma inseq_agree {G} (HG : incl ZF0base G) (HX : WOx G) q w h h' n u u' : G ⊢C Om0 w ->
  G ⊢C InSeq q w h -> G ⊢C InSeq q w h' -> G ⊢C n ∈' w -> G ⊢C App0 h n u -> G ⊢C App0 h' n u' -> G ⊢C u ≡' u'.
Proof.
  intros Hw H1 H2 Hn Hu Hu'. unfold InSeq in H1, H2. fdestr H1 H1a H1b. fdestr H1a Hf Hd. fdestr H2 H2a H2b. fdestr H2a Hf' Hd'.
  pose proof (w_om_ord HG HX w Hw) as Ow.
  exact (w_rec_agree HG HX Sin fb_Sin (in_rec_Sin HX) q w w h h' n u u' (Sin_loc HG HX q) (Sin_fun HG HX q)
           Ow Hf Hd H1b Ow Hf' Hd' H2b Hn Hn Hu Hu').
Qed.

Lemma inseq_unique {G} (HG : incl ZF0base G) (HX : WOx G) q w h h' : G ⊢C Om0 w ->
  G ⊢C InSeq q w h -> G ⊢C InSeq q w h' -> G ⊢C h ≡' h'.
Proof.
  intros Hw H1 H2. pose proof H1 as H1'. pose proof H2 as H2'. unfold InSeq in H1', H2'.
  fdestr H1' H1a H1b. fdestr H1a Hf Hd. fdestr H2' H2a H2b. fdestr H2a Hf' Hd'.
  apply (wo_fun_ext HG HX h h' w Hf Hf' Hd Hd'). fall n. fintro Hn. fall u. fall u'. fintro Hu. fintro Hu'.
  exact (inseq_agree HG HX q w h h' n u u' Hw H1 H2 Hn Hu Hu').
Qed.

Lemma inseq_ex {G} (HG : incl ZF0base G) (HX : WOx G) q w : G ⊢C Om0 w -> G ⊢C ∃ InSeq q`[↑] w`[↑] $0.
Proof.
  intros Hw. pose proof (w_rec_ex HG HX Sin fb_Sin (in_rec_Sin HX) q w (Sin_loc HG HX q) (Sin_tot HG HX q) (Sin_fun HG HX q)
    (w_om_ord HG HX w Hw)) as T. fex T h Hh. fexists h. unfold InSeq. exact Hh.
Qed.

(** the value of an inner sequence at n satisfies [Sin] *)
Lemma inseq_val {G} (HG : incl ZF0base G) (HX : WOx G) q w h n u : G ⊢C InSeq q w h -> G ⊢C App0 h n u ->
  G ⊢C SR Sin h n u q.
Proof.
  intros H Hu. unfold InSeq in H. pose proof (CE2 H) as H2. unfold RecOK in H2.
  pose proof (w_pairsall_use HG HX h _ n u H2 Hu) as T. simp_in T. exact T.
Qed.

(** ** PairSet with equivalent formulas *)
Lemma pairset_equiv {G} (HG : incl ZF0base G) (HX : WOx G) B W phi phi' :
  (forall G' z z', incl G G' -> G' ⊢C phi[z' .: z .: var] -> G' ⊢C phi'[z' .: z .: var]) ->
  (forall G' z z', incl G G' -> G' ⊢C phi'[z' .: z .: var] -> G' ⊢C phi[z' .: z .: var]) ->
  G ⊢C PairSet B W phi -> G ⊢C PairSet B W phi'.
Proof.
  intros Himp Himp' H. pose proof (incl_refl G) as Hinc. pose proof H as H0. unfold PairSet in H0 |- *. fall p. fsplit.
  - fintro Hp. finst H0 p. pose proof (iff_l _ _ _ H0 Hp) as T. clear H0.
    fex T z Hz. fdestr Hz Hz1 Hz2. fex Hz2 z' Hz'. fdestr Hz' Hz3 Hz4. fdestr Hz4 Hop Hph.
    pose proof (w_app0_intro HG HX W z z' p Hop Hp) as A.
    pose proof (CE2 (pairset_el HG HX B W phi z z' H A)) as P. apply Himp in P; [|exact Hinc].
    fexists z. fsplit; [exact Hz1|]. fexists z'. fsplit; [exact Hz3|]. fsplit; [exact Hop|].
    rewrite !subst_comp. erewrite subst_ext; [exact P|].
    intros [|[|k]]; cbn; unfold funcomp; cbn; rewrite ?subst_term_shift, ?shift_scons_term; reflexivity.
  - fintro Hp. fex Hp z Hz. fdestr Hz Hz1 Hz2. fex Hz2 z' Hz'. fdestr Hz' Hz3 Hz4. fdestr Hz4 Hop Hph.
    fassert P : (phi'[z' .: z .: var]).
    { rewrite !subst_comp in Hph. eapply leib_gen; [exact HG| |exact Hph].
      intros [|[|k]]; cbn; unfold funcomp; cbn; rewrite ?subst_term_shift, ?shift_scons_term; apply (eq_refl' HG). }
    apply Himp' in P; [|exact Hinc].
    pose proof (pairset_in HG HX B W phi z z' H Hz1 Hz3 P) as A. unfold App0 in A. fex A q Hq. fdestr Hq Hq1 Hq2.
    pose proof (w_op0_unique HG HX _ _ _ _ Hq2 Hop) as E. fmem.
Qed.


(** ** Accessing the pairs h(n) = (B_n, W_n) *)
Lemma inb_el {G} (HG : incl ZF0base G) (HX : WOx G) h n z u B W : G ⊢C Fun0 h -> G ⊢C App0 h n u -> G ⊢C OP0 B W u ->
  G ⊢C InB h n z -> G ⊢C z ∈' B.
Proof.
  intros Hf Hu Hop H. unfold InB in H. fex H u' Hu'. fdestr Hu' Hu1 Hu2. fex Hu2 B' HB'. fex HB' W' HW'. fdestr HW' Hop' Hz.
  pose proof (w_fun0_app HG HX h n u u' Hf Hu Hu1) as E. frew_in E (OP0 B'`[↑] W'`[↑] $0) Hop'.
  pose proof (w_op0_inj HG HX _ _ _ _ _ Hop Hop') as E2. fdestr E2 E3 E4. fmem.
Qed.
Lemma inb_intro {G} h n z u B W : G ⊢C App0 h n u -> G ⊢C OP0 B W u -> G ⊢C z ∈' B -> G ⊢C InB h n z.
Proof.
  intros Hu Hop Hz. unfold InB. fexists u. fsplit; [exact Hu|]. fexists B. fexists W. fsplit; [exact Hop|exact Hz].
Qed.
Lemma appw_el {G} (HG : incl ZF0base G) (HX : WOx G) h n z z' u B W : G ⊢C Fun0 h -> G ⊢C App0 h n u -> G ⊢C OP0 B W u ->
  G ⊢C AppW h n z z' -> G ⊢C App0 W z z'.
Proof.
  intros Hf Hu Hop H. unfold AppW in H. fex H u' Hu'. fdestr Hu' Hu1 Hu2. fex Hu2 B' HB'. fex HB' W' HW'. fdestr HW' Hop' Hz.
  pose proof (w_fun0_app HG HX h n u u' Hf Hu Hu1) as E. frew_in E (OP0 B'`[↑] W'`[↑] $0) Hop'.
  pose proof (w_op0_inj HG HX _ _ _ _ _ Hop Hop') as E2. fdestr E2 E3 E4.
  frew_in E4 (App0 $0 z`[↑] z'`[↑]) Hz. exact Hz.
Qed.
Lemma appw_intro {G} h n z z' u B W : G ⊢C App0 h n u -> G ⊢C OP0 B W u -> G ⊢C App0 W z z' -> G ⊢C AppW h n z z'.
Proof.
  intros Hu Hop Hz. unfold AppW. fexists u. fsplit; [exact Hu|]. fexists B. fexists W. fsplit; [exact Hop|exact Hz].
Qed.

Lemma fb_InvF : fb 3 InvF.  Proof. fbcomp. Qed.
Lemma fb_InBf : fb 3 InBf.  Proof. fbcomp. Qed.
Lemma fb_LRf_RkI : fb 4 (LRf RkI).  Proof. fbcomp. Qed.
Lemma fb_SRf_RkI : fb 4 (SRf RkI).  Proof. fbcomp. Qed.

(** ** The inner invariant: h(n) = (g(n), W_n) with W_n a well-order of g(n), where g is the
    stage function of Cl(B0) *)
Lemma inner_inv {G} (HG : incl ZF0base G) (HX : WOx G) q B0 W0 w h g w' :
  G ⊢C OP0 B0 W0 q -> G ⊢C WO W0 B0 -> G ⊢C Om0 w -> G ⊢C InSeq q w h ->
  G ⊢C Om0 w' -> G ⊢C Fun0 g -> G ⊢C Dom0 g w' -> G ⊢C RecOK Scl B0 g ->
  G ⊢C ∀ ($0 ∈' w`[↑] → ∃ (App0 h`[↑]`[↑] $1 $0 ∧ ∃ (∃ (OP0 $1 $0 $2 ∧ (WO $0 $1 ∧ App0 g`[↑]`[↑]`[↑]`[↑] $3 $1))))).
Proof.
  intros Hq HW0 Hw Hh Hw' Hg Hgd Hgr.
  pose proof (w_om_unique HG HX w w' Hw Hw') as Eww. frew_in Eww (Dom0 g`[↑] $0) Hgd.
  pose proof Hh as Hh'. unfold InSeq in Hh'. fdestr Hh' Hh1 Hhr. fdestr Hh1 Hhf Hhd.
  getinst Hin1 (forall_times 2 (ax_sep' InvF)). pose proof (sep_use _ 2 InvF (h .: g .: var) w Hin1 fb_InvF) as T. unfold InvF in T. simp_in T. fex T X HXc.
  fassert Hsub : (Sub0 w X).
  { apply (w_om_ind HG HX w X Hw).
    - fall e. fintro He. pose proof HXc as H. finst H e. apply (iff_r _ _ _ H). clear H.
      pose proof (w_om_emp HG HX w e Hw He) as Hew. fsplit; [exact Hew|].
      fobtain (w_dom0_app HG HX h w e Hhd Hew) as u Hu.
      pose proof (inseq_val HG HX q w h e u Hh Hu) as Su. rewrite Sin_eq in Su.
      pose proof (CE1 (CE1 Su)) as Su1. fmp Su1 He.
      fobtain (w_dom0_app HG HX g w e Hgd Hew) as x Hx.
      unfold RecOK in Hgr. pose proof (w_pairsall_use HG HX g _ e x Hgr Hx) as Sx. simp_in Sx. rewrite Scl_eq in Sx.
      pose proof (CE1 (CE1 Sx)) as Sx1. fmp Sx1 He.
      fexists u. fsplit; [exact Hu|]. fexists B0. fexists W0. fsplit; [|fsplit; [exact HW0|]].
      + frew_in Su1 (OP0 B0`[↑] W0`[↑] $0) Hq. exact Hq.
      + frew_in Sx1 (App0 g`[↑] e`[↑] $0) Hx. exact Hx.
    - fall n. fintro Hn. fintro HnX. fall s. fintro Hs.
      pose proof HXc as H. finst H n. pose proof (CE2 (iff_l _ _ _ H HnX)) as Inv. clear H.
      fex Inv u Hu. fdestr Hu Hu1 Hu2. fex Hu2 B HB. fex HB W HW. fdestr HW HW1 HW2. fdestr HW2 HWB HgB.
      pose proof (w_om_succ HG HX w n s Hw Hn Hs) as Hsw.
      fobtain (w_dom0_app HG HX h w s Hhd Hsw) as us Hus.
      pose proof (inseq_val HG HX q w h s us Hh Hus) as Su. rewrite Sin_eq in Su.
      pose proof (CE2 (CE1 Su)) as Su2. finst Su2 n. fmp Su2 (wo_succ_in n s Hs). fmp Su2 Hs. fex Su2 u' Hu'. fdestr Hu' Hu1' Hnx.
      pose proof (w_fun0_app HG HX h n u u' Hhf Hu1 Hu1') as Euu. frew_in Euu (NextP $0 us`[↑]) Hnx.
      unfold NextP in Hnx. fcases Hnx N1 N2.
      2: { fdestr N2 N3 N4. finst N3 B W. fabsurd. exact (IE N3 HW1). }
      fex N1 B1 HB1. fex HB1 W1 HW1'. fdestr HW1' HO1 HN. fex HN B' HB'. fex HB' W' HW'. fdestr HW' HO2 HNx.
      pose proof (w_op0_inj HG HX _ _ _ _ _ HW1 HO1) as E. fdestr E E1 E2.
      frew_in E1 (NxR $0 W1`[↑] B'`[↑] W'`[↑]) HNx. frew_in E2 (NxR B`[↑] $0 B'`[↑] W'`[↑]) HNx.
      unfold NxR in HNx. fdestr HNx HSt HPS.
      fobtain (w_dom0_app HG HX g w s Hgd Hsw) as xs Hxs.
      unfold RecOK in Hgr. pose proof (w_pairsall_use HG HX g _ s xs Hgr Hxs) as Sx. simp_in Sx. rewrite Scl_eq in Sx.
      pose proof (CE2 (CE1 Sx)) as Sx2. finst Sx2 n. fmp Sx2 (wo_succ_in n s Hs). fmp Sx2 Hs. fex Sx2 x Hx. fdestr Hx Hx1 Hx2.
      pose proof (w_fun0_app HG HX g n B x Hg HgB Hx1) as Ex. frew_in Ex (Step $0 xs`[↑]) Hx2.
      pose proof (w_step_unique HG HX _ _ _ HSt Hx2) as Exs.
      fassert HWB' : (WO W' B').
      { apply (sum_wo HG HX NOf B' B W W' B W).
        - unfold Step in HSt. exact (CE1 (CE1 HSt)).
        - exact HWB.
        - exact (new_wo_least HG HX B B' W HWB HSt).
        - exact (new_wo_asym HG B B' W HWB).
        - fall z. fintro Hz. fall z'. fintro Hz'. fsplit.
          + fintro H. pose proof (CE2 (pairset_el HG HX _ _ _ z z' HPS H)) as H'. simp_in H'. exact H'.
          + fintro H. apply (pairset_in HG HX _ _ _ z z' HPS Hz Hz'). simp. exact H. }
      pose proof HXc as H. finst H s. apply (iff_r _ _ _ H). clear H. fsplit; [exact Hsw|].
      fexists us. fsplit; [exact Hus|]. fexists B'. fexists W'. fsplit; [exact HO2|]. fsplit; [exact HWB'|].
      frew_in Exs (App0 g`[↑] s`[↑] $0) Hxs. exact Hxs. }
  fall n. fintro Hn. pose proof HXc as H. finst H n. exact (CE2 (iff_l _ _ _ H (wo_sub0_use HG _ _ _ Hsub Hn))).
Qed.

(** ** The stage-first order of Def(Y) is a well-order *)
Lemma cst_wo {G} (HG : incl ZF0base G) (HX : WOx G) h w D v Y B0 W0 q :
  G ⊢C Om0 w -> G ⊢C InSeq q w h -> G ⊢C OP0 B0 W0 q -> G ⊢C WO W0 B0 -> G ⊢C Succ0 Y B0 -> G ⊢C Def0 Y D ->
  G ⊢C CstOrd h w D v -> G ⊢C WO v D.
Proof.
  intros Hw Hh Hq HW0 HY HD Hv.
  pose proof Hh as Hh'. unfold InSeq in Hh'. fdestr Hh' Hh1 Hhr. fdestr Hh1 Hhf Hhd.
  pose proof (w_om_ord HG HX w Hw) as Ow.
  unfold Def0 in HD. fex HD B1 HB1. fex HB1 C HC. fdestr HC HC1 HC4. fdestr HC1 HC2 HDC. fdestr HC2 HYB1 HCl.
  pose proof (w_succ0_unique HG HX Y B1 B0 HYB1 HY) as EB.
  unfold Cl in HCl. fex HCl w' Hw'. fex Hw' g Hg. fdestr Hg Hg1 HRan. fdestr Hg1 Hg2 Hgr. fdestr Hg2 Hg3 Hgd. fdestr Hg3 Hw'o Hgf.
  frew_in EB (RecOK Scl $0 g`[↑]) Hgr.
  pose proof (inner_inv HG HX q B0 W0 w h g w' Hq HW0 Hw Hh Hw'o Hgf Hgd Hgr) as Inv.
  pose proof (w_om_unique HG HX w w' Hw Hw'o) as Eww. frew_in Eww (Dom0 g`[↑] $0) Hgd.
  (* every element of D is in some stage *)
  fassert HDst : (∀ ($0 ∈' D`[↑] → ∃ ($0 ∈' w`[↑]`[↑] ∧ InB h`[↑]`[↑] $0 $1))).
  { fall z. fintro Hz. pose proof HDC as H. finst H z. fmp H Hz. pose proof (CE1 H) as HzC. clear H.
    unfold RanU in HRan. pose proof (CE1 HRan) as R. finst R z. fmp R HzC.
    fex R p Hp. fdestr Hp Hp1 Hp2. fex Hp2 s Hs. fdestr Hs Hs1 Hs2. fex Hs2 x Hx. fdestr Hx Hx1 Hx2. fdestr Hx2 Hzx Hx3.
    fex Hx3 s' Hs'. fdestr Hs' Hs1' Hs2'. fex Hs2' n Hn. fdestr Hn Hn1 Hop.
    pose proof (w_app0_intro HG HX g n x p Hop Hp1) as Hgx.
    pose proof (w_dom0_in HG HX g w n x Hgd Hgx) as Hnw.
    pose proof Inv as I. finst I n. fmp I Hnw. fex I u Hu. fdestr Hu Hu1 Hu2. fex Hu2 B HB. fex HB W HW. fdestr HW HW1 HW2.
    fdestr HW2 HWB HgB. pose proof (w_fun0_app HG HX g n x B Hgf Hgx HgB) as Ex.
    fexists n. fsplit; [exact Hnw|]. apply (inb_intro h n z u B W Hu1 HW1). fmem. }
  (* the rank of an element *)
  fassert Hrank : (∀ ($0 ∈' D`[↑] → ∃ (Ord0 $0 ∧ ($0 ∈' w`[↑]`[↑] ∧ St h`[↑]`[↑] $0 $1)))).
  { fall z. fintro Hz. pose proof HDst as H. finst H z. fmp H Hz. fex H n0 Hn0. fdestr Hn0 Hn0w Hn0z.
    getinst Hin2 (least_inst 2 InBf). pose proof (w_least_ord HG HX 2 InBf (h .: z .: var) n0 fb_InBf Hin2 (w_ord_el HG HX w n0 Ow Hn0w)) as T.
    unfold InBf in T. simp_in T. specialize (T Hn0z). fex T n Hn. fdestr Hn Hn1 Hmin. fdestr Hn1 On Hnz.
    fexists n. fsplit; [exact On|]. fsplit; [|unfold St; fsplit; [exact Hnz|exact Hmin]].
    pose proof (w_ord_tri HG HX n n0 On (w_ord_el HG HX w n0 Ow Hn0w)) as Tr. fcases Tr Tr1 Tr2; [fcases Tr1 Tr3 Tr4|].
    - exact (w_ord_tr HG HX w n n0 Ow Tr3 Hn0w).
    - fmem.
    - fabsurd. finst Hmin n0. fmp Hmin Tr2. exact (IE Hmin Hn0z). }
  apply (sf_wo HG HX RkI OwI D v h w).
  - unfold I4, RkI. simp. exact Hrank.
  - unfold I4, RkI. simp. fall z. fintro Hz. fall e. fall e'. fintro He. fintro He'.
    fdestr He He1 He2. fdestr He' He1' He2'. unfold St in He2, He2'. fdestr He2 Hez Hemin. fdestr He2' Hez' Hemin'.
    pose proof (w_ord_el HG HX w e Ow He1) as Oe. pose proof (w_ord_el HG HX w e' Ow He1') as Oe'.
    pose proof (w_ord_tri HG HX e e' Oe Oe') as Tr. fcases Tr Tr1 Tr2; [fcases Tr1 Tr3 Tr4|].
    + fabsurd. finst Hemin' e. fmp Hemin' Tr3. exact (IE Hemin' Hez).
    + exact Tr4.
    + fabsurd. finst Hemin e'. fmp Hemin Tr2. exact (IE Hemin Hez').
  - fall T. fintro HT. fintro Hne. fex Hne z Hz.
    pose proof Hrank as H. finst H z. fmp H (wo_sub0_use HG _ _ _ HT Hz). fex H e He. fdestr He Oe Hez.
    getinst Hin3 (least_inst 3 (LRf RkI)). pose proof (w_least_ord HG HX 3 (LRf RkI) (T .: h .: w .: var) e fb_LRf_RkI Hin3 Oe) as L.
    unfold LRf in L. simp_in L. apply L. fexists z. fsplit; [exact Hz|]. unfold I4, RkI. simp. exact Hez.
  - fall T. fall e. getinst Hin4 (forall_times 3 (ax_sep' (SRf RkI))). pose proof (sep_use _ 3 (SRf RkI) (e .: h .: w .: var) T Hin4 fb_SRf_RkI) as S. unfold SRf in S. simp_in S. exact S.
  - unfold I4, I5, RkI, OwI. simp. fall e. fintro Oe. fall y. fintro Hy. fintro Hne. fex Hne u0 Hu0.
    pose proof Hy as H. finst H u0. fmp H Hu0. fdestr H H1 H2. fdestr H2 He Hst.
    pose proof Inv as I. finst I e. fmp I He. fex I u Hu. fdestr Hu Hu1 Hu2. fex Hu2 B HB. fex HB W HW. fdestr HW HW1 HW2.
    fdestr HW2 HWB HgB.
    fassert HyB : (Sub0 y B).
    { unfold Sub0. fall z. fintro Hz. pose proof Hy as H'. finst H' z. fmp H' Hz. fdestr H' H3 H4. fdestr H4 H5 H6.
      unfold St in H6. exact (inb_el HG HX h e z u B W Hhf Hu1 HW1 (CE1 H6)). }
    pose proof (wo_least W B y u0 HWB HyB Hu0) as L. fex L m Hm. fexists m. fsplit; [exact (lst_in _ _ _ Hm)|].
    fall z. fintro Hz. fintro Hzm. exact (appw_intro h e m z u B W Hu1 HW1 (lst_lt W y m z Hm Hz Hzm)).
  - unfold I4, I5, RkI, OwI. simp. fall e. fintro Oe. fall a. fintro Ha. fall b. fintro Hb.
    fintro Ra. fintro Rb. fintro A1. fintro A2. fdestr Ra Ra1 Ra2. fdestr Rb Rb1 Rb2. unfold St in Ra2, Rb2.
    pose proof Inv as I. finst I e. fmp I Ra1. fex I u Hu. fdestr Hu Hu1 Hu2. fex Hu2 B HB. fex HB W HW. fdestr HW HW1 HW2.
    fdestr HW2 HWB HgB.
    pose proof (inb_el HG HX h e a u B W Hhf Hu1 HW1 (CE1 Ra2)) as HaB.
    pose proof (inb_el HG HX h e b u B W Hhf Hu1 HW1 (CE1 Rb2)) as HbB.
    exact (wo_asym W B a b HWB HaB HbB (appw_el HG HX h e a b u B W Hhf Hu1 HW1 A1) (appw_el HG HX h e b a u B W Hhf Hu1 HW1 A2)).
  - fall z. fintro Hz. fall z'. fintro Hz'. unfold CstOrd in Hv. fsplit.
    + fintro H. pose proof (CE2 (pairset_el HG HX _ _ _ z z' Hv H)) as H'. simp_in H'. exact H'.
    + fintro H. apply (pairset_in HG HX _ _ _ z z' Hv Hz Hz'). simp. exact H.
Qed.

#[local] Ltac unpack_out H Y Oo B W0 q w h D HY HO HB HW0 Hq Hw Hh HD Hv :=
  let T1 := fresh "T1x" in let T2 := fresh "T2x" in let T3 := fresh "T3x" in let T4 := fresh "T4x" in
  let T5 := fresh "T5x" in let T6 := fresh "T6x" in let T7 := fresh "T7x" in let T8 := fresh "T8x" in
  let T9 := fresh "T9x" in let T10 := fresh "T10x" in let T11 := fresh "T11x" in let T12 := fresh "T12x" in
  let T13 := fresh "T13x" in let T14 := fresh "T14x" in let T15 := fresh "T15x" in
  fex H Y T1; fdestr T1 HY T2; fex T2 Oo T3; fdestr T3 HO T4; fex T4 B T5; fdestr T5 HB T6;
  fex T6 W0 T7; fdestr T7 HW0 T8; fex T8 q T9; fdestr T9 Hq T10; fex T10 w T11; fdestr T11 Hw T12;
  fex T12 h T13; fdestr T13 Hh T14; fex T14 D T15; fdestr T15 HD Hv.

Lemma fb_phRho : fb 4 phRho.  Proof. fbcomp. Qed.
Lemma fb_phSum0 : fb 4 phSum0.  Proof. fbcomp. Qed.
Lemma fb_phCst : fb 4 phCst.  Proof. fbcomp. Qed.
Lemma fb_InL1f : fb 2 InL1f.  Proof. fbcomp. Qed.
Lemma fb_LRf_RkO : fb 4 (LRf RkO).  Proof. fbcomp. Qed.
Lemma fb_SRf_RkO : fb 4 (SRf RkO).  Proof. fbcomp. Qed.
Lemma fb_Sout : fb 4 Sout.  Proof. fbcomp. Qed.
Lemma fb_psi_ind : fb 3 psi_ind.  Proof. fbcomp. Qed.
Lemma fb_ChF : fb 3 ChF.  Proof. fbcomp. Qed.

Lemma Sout_eq F xi v p : SR Sout F xi v p = OutP F xi v.
Proof. unfold SR, Sout. simp. reflexivity. Qed.

Lemma in_rec_Sout {G} (HX : WOx G) : incl (rec_insts Sout) G.
Proof. intros a Ha. apply (in_wo HX). unfold wo_list. rewrite !in_app_iff. tauto. Qed.

(** ** Ranks in L *)
Lemma inl1_ex {G} (HG : incl ZF0base G) (HX : WOx G) xi Y z : G ⊢C Ord0 xi -> G ⊢C LL xi Y -> G ⊢C z ∈' Y ->
  G ⊢C ∃ ($0 ∈' xi`[↑] ∧ InL1 z`[↑] $0).
Proof.
  intros Oxi HY Hz. pose proof (w_ord_cases HG HX xi Oxi) as C. fcases C C1 C2; [fcases C1 C3 C4|].
  - fabsurd. exact (wo_emp_el Y z (w_LL_zero HG HX xi Y C3 HY) Hz).
  - fex C4 m Hm. fdestr Hm Om Hms. fexists m. fsplit; [exact (wo_succ_in m xi Hms)|].
    unfold InL1. fexists xi. fsplit; [exact Hms|]. fexists Y. fsplit; [exact HY|exact Hz].
  - pose proof (w_LL_lim HG HX xi Y C2 HY) as L. finst L z. fmp L Hz. fex L e He. fdestr He He1 He2.
    fex He2 Ye HYe. fdestr HYe HYe1 HYe2.
    pose proof (w_ord_el HG HX xi e Oxi He1) as Oe.
    fobtain (w_succ0_ex HG HX e) as s Hs. pose proof (w_ord_succ HG HX e s Oe Hs) as Os.
    fobtain (w_LL_ex HG HX s Os) as Ys HYs.
    pose proof (w_LL_mono HG HX s e Ys Ye Os (wo_succ_in e s Hs) HYs HYe1) as M. fdestr M M1 M2.
    fexists e. fsplit; [exact He1|]. unfold InL1. fexists s. fsplit; [exact Hs|]. fexists Ys. fsplit; [exact HYs|].
    exact (wo_sub0_use HG _ _ _ M2 HYe2).
Qed.

Lemma rho_ex {G} (HG : incl ZF0base G) (HX : WOx G) xi Y z : G ⊢C Ord0 xi -> G ⊢C LL xi Y -> G ⊢C z ∈' Y ->
  G ⊢C ∃ (Ord0 $0 ∧ ($0 ∈' xi`[↑] ∧ Rho z`[↑] $0)).
Proof.
  intros Oxi HY Hz. pose proof (inl1_ex HG HX xi Y z Oxi HY Hz) as T. fex T e0 He0. fdestr He0 He0x He0z.
  pose proof (w_ord_el HG HX xi e0 Oxi He0x) as Oe0.
  getinst Hin1 (least_inst 1 InL1f). pose proof (w_least_ord HG HX 1 InL1f (z .: var) e0 fb_InL1f Hin1 Oe0) as L. unfold InL1f in L. simp_in L.
  specialize (L He0z). fex L e He. fdestr He He1 Hmin. fdestr He1 Oe Hez.
  fexists e. fsplit; [exact Oe|]. fsplit; [|unfold Rho; fsplit; [exact Hez|exact Hmin]].
  pose proof (w_ord_tri HG HX e e0 Oe Oe0) as Tr. fcases Tr Tr1 Tr2; [fcases Tr1 Tr3 Tr4|].
  - exact (w_ord_tr HG HX xi e e0 Oxi Tr3 He0x).
  - fmem.
  - fabsurd. finst Hmin e0. fmp Hmin Tr2. exact (IE Hmin He0z).
Qed.

Lemma rho_unique {G} (HG : incl ZF0base G) (HX : WOx G) z e e' : G ⊢C Ord0 e -> G ⊢C Ord0 e' ->
  G ⊢C Rho z e -> G ⊢C Rho z e' -> G ⊢C e ≡' e'.
Proof.
  intros Oe Oe' H1 H2. unfold Rho in H1, H2. fdestr H1 H1a H1b. fdestr H2 H2a H2b.
  pose proof (w_ord_tri HG HX e e' Oe Oe') as Tr. fcases Tr Tr1 Tr2; [fcases Tr1 Tr3 Tr4|].
  - fabsurd. finst H2b e. fmp H2b Tr3. exact (IE H2b H1a).
  - exact Tr4.
  - fabsurd. finst H1b e'. fmp H1b Tr2. exact (IE H1b H2a).
Qed.

Lemma inl1_lev {G} (HG : incl ZF0base G) (HX : WOx G) z e s Ys : G ⊢C Ord0 e -> G ⊢C Succ0 e s -> G ⊢C LL s Ys ->
  G ⊢C InL1 z e -> G ⊢C z ∈' Ys.
Proof.
  intros Oe Hs HYs H. unfold InL1 in H. fex H s' Hs'. fdestr Hs' Hs1 Hs2. fex Hs2 Y' HY'. fdestr HY' HY1 HY2.
  pose proof (w_succ0_unique HG HX e s s' Hs Hs1) as E. frew_in E (LL $0 Y'`[↑]) HY1.
  pose proof (w_LL_unique HG HX s Ys Y' (w_ord_succ HG HX e s Oe Hs) HYs HY1) as E2. fmem.
Qed.

(** ** The outer step formula *)
Lemma wo_agree_sym {G} (HG : incl ZF0base G) F F' xi : G ⊢C Agree F F' xi -> G ⊢C Agree F' F xi.
Proof.
  intros H. unfold Agree in H |- *. fall e. fintro He. fall u. finst H e. fmp H He. finst H u.
  fsplit; [exact (CE2 H)|exact (CE1 H)].
Qed.

Lemma sfr_agree {G} (HG : incl ZF0base G) F F' xi z z' : G ⊢C Agree F F' xi ->
  G ⊢C SFR RkO OwO xi F z z' -> G ⊢C SFR RkO OwO xi F' z z'.
Proof.
  intros HA H. unfold SFR in H |- *. fex H e He. fex He e' He'. fdestr He' H1 H2. fdestr H1 H3 H4.
  fexists e. fexists e'. unfold I4, I5, RkO, OwO in *. simp. simp_in H3. simp_in H4. simp_in H2.
  fsplit; [fsplit; assumption|]. fcases H2 H5 H6; [fleft; exact H5|]. fright. fdestr H6 H7 H8. fsplit; [exact H7|].
  fex H8 Wc HWc. fdestr HWc HW1 HW2. fexists Wc. fsplit; [|exact HW2].
  unfold Agree in HA. finst HA e. fmp HA (CE1 H3). finst HA Wc. exact (iff_l _ _ _ HA HW1).
Qed.

Lemma rhoord_agree {G} (HG : incl ZF0base G) (HX : WOx G) F F' xi Y Oo : G ⊢C Agree F F' xi ->
  G ⊢C RhoOrd xi F Y Oo -> G ⊢C RhoOrd xi F' Y Oo.
Proof.
  intros HA H. unfold RhoOrd in H |- *. apply (pairset_equiv HG HX Y Oo (SFR RkO OwO xi`[↑]`[↑] F`[↑]`[↑] $1 $0) (SFR RkO OwO xi`[↑]`[↑] F'`[↑]`[↑] $1 $0)); [| |exact H].
  - intros G' z z' Hinc P. simp_in P. simp. apply (sfr_agree (incl_tran HG Hinc) F F' xi z z'); [|exact P].
    eapply Weak; [exact HA|exact Hinc].
  - intros G' z z' Hinc P. simp_in P. simp. apply (sfr_agree (incl_tran HG Hinc) F' F xi z z'); [|exact P].
    eapply Weak; [exact (wo_agree_sym HG F F' xi HA)|exact Hinc].
Qed.

Lemma Sout_loc {G} (HG : incl ZF0base G) (HX : WOx G) p : G ⊢C SLoc Sout p.
Proof.
  unfold SLoc. fall F. fall F'. fall xi. fall v. fintro Hf. fintro Hf'. fintro Hxi. fintro HA. fintro H.
  rewrite Sout_eq in H |- *. unfold OutP in H |- *.
  fex H Y HY. fdestr HY HY1 HY2. fex HY2 Oo HO. fdestr HO HO1 HO2.
  fexists Y. fsplit; [exact HY1|]. fexists Oo. fsplit; [|exact HO2]. exact (rhoord_agree HG HX F F' xi Y Oo HA HO1).
Qed.

Lemma Sout_tot {G} (HG : incl ZF0base G) (HX : WOx G) p : G ⊢C STot Sout p.
Proof.
  unfold STot. fall F. fall xi. fintro Hf. fintro Hxi. fintro Hval.
  fobtain (w_LL_ex HG HX xi Hxi) as Y HY.
  getinst Hin2 (forall_times 3 (ax_sep' (PSF phRho))). pose proof (pairset_ex HG 2 phRho (xi .: F .: var) Y fb_phRho Hin2) as T. unfold phRho in T. simp_in T.
  fex T Oo HO.
  fobtain (w_succ0_ex HG HX Y) as B HB.
  getinst Hin3 (forall_times 3 (ax_sep' (PSF phSum0))). pose proof (pairset_ex HG 2 phSum0 (Y .: Oo .: var) B fb_phSum0 Hin3) as T. unfold phSum0 in T. simp_in T.
  fex T W0 HW0.
  fobtain (w_op0_ex HG HX B W0) as q Hq.
  fobtain (w_om_ex HG HX) as w Hw.
  fobtain (inseq_ex HG HX q w Hw) as h Hh.
  fobtain (w_def_ex HG HX Y) as D HD.
  getinst Hin4 (forall_times 3 (ax_sep' (PSF phCst))). pose proof (pairset_ex HG 2 phCst (h .: w .: var) D fb_phCst Hin4) as T. unfold phCst in T. simp_in T.
  fex T v Hv.
  fexists v. rewrite Sout_eq. unfold OutP.
  fexists Y. fsplit; [exact HY|]. fexists Oo. fsplit; [unfold RhoOrd; exact HO|].
  fexists B. fsplit; [exact HB|]. fexists W0. fsplit; [unfold Sum0; exact HW0|].
  fexists q. fsplit; [exact Hq|]. fexists w. fsplit; [exact Hw|]. fexists h. fsplit; [exact Hh|].
  fexists D. fsplit; [exact HD|]. unfold CstOrd. exact Hv.
Qed.

Lemma Sout_fun {G} (HG : incl ZF0base G) (HX : WOx G) p : G ⊢C SFun Sout p.
Proof.
  unfold SFun. fall F. fall xi. fall v. fall v'. fintro Hf. fintro Hxi. fintro H1. fintro H2.
  rewrite Sout_eq in H1, H2. unfold OutP in H1, H2.
  unpack_out H1 Y Oo B W0 q w h D HY HO HB HW0 Hq Hw Hh HD Hv.
  unpack_out H2 Y' Oo' B' W0' q' w' h' D' HY' HO' HB' HW0' Hq' Hw' Hh' HD' Hv'.
  pose proof (w_LL_unique HG HX xi Y Y' Hxi HY HY') as EY.
  frew_in EY (RhoOrd xi`[↑] F`[↑] $0 Oo'`[↑]) HO'.
  unfold RhoOrd in HO, HO'. pose proof (pairset_unique HG _ _ _ _ HO HO') as EO.
  frew_in EY (Succ0 $0 B'`[↑]) HB'. pose proof (w_succ0_unique HG HX Y B B' HB HB') as EB.
  frew_in EY (Sum0 $0 Oo'`[↑] B'`[↑] W0'`[↑]) HW0'. frew_in EO (Sum0 Y`[↑] $0 B'`[↑] W0'`[↑]) HW0'.
  frew_in EB (Sum0 Y`[↑] Oo`[↑] $0 W0'`[↑]) HW0'.
  unfold Sum0 in HW0, HW0'. pose proof (pairset_unique HG _ _ _ _ HW0 HW0') as EW.
  frew_in EB (OP0 $0 W0'`[↑] q'`[↑]) Hq'. frew_in EW (OP0 B`[↑] $0 q'`[↑]) Hq'.
  pose proof (w_op0_unique HG HX _ _ _ _ Hq Hq') as Eq.
  pose proof (w_om_unique HG HX w w' Hw Hw') as Ew.
  frew_in Eq (InSeq $0 w'`[↑] h'`[↑]) Hh'. frew_in Ew (InSeq q`[↑] $0 h'`[↑]) Hh'.
  pose proof (inseq_unique HG HX q w h h' Hw Hh Hh') as Eh.
  frew_in EY (Def0 $0 D'`[↑]) HD'. pose proof (w_def_unique HG HX Y D D' HD HD') as ED.
  frew_in Eh (CstOrd $0 w'`[↑] D'`[↑] v'`[↑]) Hv'. frew_in Ew (CstOrd h`[↑] $0 D'`[↑] v'`[↑]) Hv'.
  frew_in ED (CstOrd h`[↑] w`[↑] $0 v'`[↑]) Hv'.
  unfold CstOrd in Hv, Hv'. exact (pairset_unique HG _ _ _ _ Hv Hv').
Qed.

(** ** The outer induction step *)
Lemma outer_step {G} (HG : incl ZF0base G) (HX : WOx G) F d p : G ⊢C Ord0 d -> G ⊢C Fun0 F -> G ⊢C Dom0 F d ->
  G ⊢C RecOK Sout p F ->
  G ⊢C ∀ (Ord0 $0 → (∀ ($0 ∈' $1 → PsiP F`[↑]`[↑] d`[↑]`[↑] $0)) → PsiP F`[↑] d`[↑] $0).
Proof.
  intros Od Hf Hd Hr. fall xi. fintro Oxi. fintro IH. unfold PsiP. fintro Hxd. fall Wc. fintro HWc.
  fall Y. fintro HY. fall D. fintro HD.
  unfold RecOK in Hr. pose proof (w_pairsall_use HG HX F _ xi Wc Hr HWc) as Hso. simp_in Hso. rewrite Sout_eq in Hso.
  unfold OutP in Hso.
  unpack_out Hso Y' Oo B W0 q w h D' HY' HO HB HW0 Hq Hw Hh HD' Hv.
  (* Oo well-orders Y' = L_ξ *)
  fassert HWO : (WO Oo Y').
  { apply (sf_wo HG HX RkO OwO Y' Oo xi F).
    - unfold I4, RkO. simp. fall z. fintro Hz. exact (rho_ex HG HX xi Y' z Oxi HY' Hz).
    - unfold I4, RkO. simp. fall z. fintro Hz. fall e. fall e'. fintro He. fintro He'. fdestr He He1 He2. fdestr He' He1' He2'.
      exact (rho_unique HG HX z e e' (w_ord_el HG HX xi e Oxi He1) (w_ord_el HG HX xi e' Oxi He1') He2 He2').
    - fall T. fintro HT. fintro Hne. fex Hne z Hz.
      pose proof (rho_ex HG HX xi Y' z Oxi HY' (wo_sub0_use HG _ _ _ HT Hz)) as R. fex R e He. fdestr He Oe Hez.
      getinst Hin5 (least_inst 3 (LRf RkO)). pose proof (w_least_ord HG HX 3 (LRf RkO) (T .: xi .: F .: var) e fb_LRf_RkO Hin5 Oe) as L.
      unfold LRf in L. simp_in L. apply L. fexists z. fsplit; [exact Hz|]. unfold I4, RkO. simp. exact Hez.
    - fall T. fall e. getinst Hin6 (forall_times 3 (ax_sep' (SRf RkO))). pose proof (sep_use _ 3 (SRf RkO) (e .: xi .: F .: var) T Hin6 fb_SRf_RkO) as S. unfold SRf in S. simp_in S. exact S.
    - unfold I4, I5, RkO, OwO. simp. fall e. fintro Oe. fall y. fintro Hy. fintro Hne. fex Hne u0 Hu0.
      pose proof Hy as H. finst H u0. fmp H Hu0. fdestr H H1 H2. fdestr H2 Hex Hrho.
      pose proof (w_ord_tr HG HX d e xi Od Hex Hxd) as Hed.
      fobtain (w_dom0_app HG HX F d e Hd Hed) as We HWe.
      fobtain (w_LL_ex HG HX e Oe) as Ye HYe.
      fobtain (w_def_ex HG HX Ye) as De HDe.
      pose proof IH as I. finst I e. fmp I Hex. unfold PsiP in I. fmp I Hed. finst I We. fmp I HWe. finst I Ye. fmp I HYe.
      finst I De. fmp I HDe. rename I into HWOe.
      fobtain (w_succ0_ex HG HX e) as s Hs. pose proof (w_ord_succ HG HX e s Oe Hs) as Os.
      fobtain (w_LL_ex HG HX s Os) as Ys HYs.
      pose proof (w_def_unique HG HX Ye De Ys HDe (w_LL_succ HG HX e s Ye Ys Oe Hs HYe HYs)) as EDs.
      fassert HyD : (Sub0 y De).
      { unfold Sub0. fall z. fintro Hz. pose proof Hy as H'. finst H' z. fmp H' Hz. fdestr H' H3 H4. fdestr H4 H5 H6.
        unfold Rho in H6. pose proof (inl1_lev HG HX z e s Ys Oe Hs HYs (CE1 H6)) as Hz'. fmem. }
      pose proof (wo_least We De y u0 HWOe HyD Hu0) as L. fex L m Hm. fexists m. fsplit; [exact (lst_in _ _ _ Hm)|].
      fall z. fintro Hz. fintro Hzm. fexists We. fsplit; [exact HWe|]. exact (lst_lt We y m z Hm Hz Hzm).
    - unfold I4, I5, RkO, OwO. simp. fall e. fintro Oe. fall a. fintro Ha. fall b. fintro Hb.
      fintro Ra. fintro Rb. fintro A1. fintro A2. fdestr Ra Ra1 Ra2. fdestr Rb Rb1 Rb2.
      pose proof (w_ord_tr HG HX d e xi Od Ra1 Hxd) as Hed.
      fobtain (w_dom0_app HG HX F d e Hd Hed) as We HWe.
      fobtain (w_LL_ex HG HX e Oe) as Ye HYe.
      fobtain (w_def_ex HG HX Ye) as De HDe.
      pose proof IH as I. finst I e. fmp I Ra1. unfold PsiP in I. fmp I Hed. finst I We. fmp I HWe. finst I Ye. fmp I HYe.
      finst I De. fmp I HDe. rename I into HWOe.
      fobtain (w_succ0_ex HG HX e) as s Hs. pose proof (w_ord_succ HG HX e s Oe Hs) as Os.
      fobtain (w_LL_ex HG HX s Os) as Ys HYs.
      pose proof (w_def_unique HG HX Ye De Ys HDe (w_LL_succ HG HX e s Ye Ys Oe Hs HYe HYs)) as EDs.
      unfold Rho in Ra2, Rb2.
      pose proof (inl1_lev HG HX a e s Ys Oe Hs HYs (CE1 Ra2)) as HaY.
      pose proof (inl1_lev HG HX b e s Ys Oe Hs HYs (CE1 Rb2)) as HbY.
      fassert HaD : (a ∈' De). { fmem. }
      fassert HbD : (b ∈' De). { fmem. }
      fex A1 W1 HW1. fdestr HW1 HW1a HW1b. fex A2 W2 HW2. fdestr HW2 HW2a HW2b.
      pose proof (w_fun0_app HG HX F e We W1 Hf HWe HW1a) as E1. pose proof (w_fun0_app HG HX F e We W2 Hf HWe HW2a) as E2.
      frew_in E1 (App0 $0 a`[↑] b`[↑]) HW1b. frew_in E2 (App0 $0 b`[↑] a`[↑]) HW2b.
      exact (wo_asym We De a b HWOe HaD HbD HW1b HW2b).
    - fall z. fintro Hz. fall z'. fintro Hz'. unfold RhoOrd in HO. fsplit.
      + fintro H. pose proof (CE2 (pairset_el HG HX _ _ _ z z' HO H)) as H'. simp_in H'. exact H'.
      + fintro H. apply (pairset_in HG HX _ _ _ z z' HO Hz Hz'). simp. exact H. }
  (* W0 well-orders B = Y' ∪ {Y'} *)
  fassert HWO0 : (WO W0 B).
  { apply (sum_wo HG HX ⊥ B Y' Oo W0 Y' Y').
    - exact (wo_succ_sub Y' B HB).
    - exact HWO.
    - fall T. fintro HT. fintro Hn. fintro Hne. fex Hne m Hm. fexists m. fsplit; [exact Hm|].
      fall u. fintro Hu. fintro Hum. fabsurd. apply (IE Hum).
      pose proof (wo_succ_el Y' B u HB (wo_sub0_use HG _ _ _ HT Hu)) as A. fcases A A1 A2; [|].
      + fabsurd. pose proof Hn as H. finst H u. exact (IE (IE H Hu) A1).
      + pose proof (wo_succ_el Y' B m HB (wo_sub0_use HG _ _ _ HT Hm)) as A. fcases A A3 A4.
        * fabsurd. pose proof Hn as H. finst H m. exact (IE (IE H Hm) A3).
        * feq.
    - fall a. fintro Ha. fall b. fintro Hb. fintro Na. fintro Nb. fintro H. unfold I4 in H. cbn in H. fintro Hdum. exact H.
    - fall z. fintro Hz. fall z'. fintro Hz'. unfold Sum0 in HW0. fsplit.
      + fintro H. pose proof (CE2 (pairset_el HG HX _ _ _ z z' HW0 H)) as H'. simp_in H'. exact H'.
      + fintro H. apply (pairset_in HG HX _ _ _ z z' HW0 Hz Hz'). simp. exact H. }
  pose proof (cst_wo HG HX h w D' Wc Y' B W0 q Hw Hh Hq HWO0 HB HD' Hv) as HWc'.
  pose proof (w_LL_unique HG HX xi Y Y' Oxi HY HY') as EY. frew_in EY (Def0 $0 D`[↑]) HD.
  pose proof (w_def_unique HG HX Y' D D' HD HD') as ED. frew_in ED (WO Wc`[↑] $0) HWc'. exact HWc'.
Qed.

(** ** Every L_α is well-ordered, hence choice sets exist *)
Lemma wo_choice' {G} (HG : incl ZF0base G) (HX : WOx G) : G ⊢C ∀ (Ord0 $0 → ∀ (LL $1 $0 → ∀ ($0 ∈' $1 → ACmat $0))).
Proof.
  fall a. fintro Oa. fall Y. fintro HY. fall x. fintro Hx.
  fobtain (w_succ0_ex HG HX a) as s Hs. pose proof (w_ord_succ HG HX a s Oa Hs) as Os.
  pose proof (w_rec_ex HG HX Sout fb_Sout (in_rec_Sout HX) a s (Sout_loc HG HX a) (Sout_tot HG HX a) (Sout_fun HG HX a) Os) as T.
  fex T F HFd. fdestr HFd HFd1 Hr. fdestr HFd1 Hf Hd.
  getinst Hin7 (least_inst 2 (¬ psi_ind)). pose proof (w_ord_ind HG HX 2 psi_ind (F .: s .: var) a fb_psi_ind Hin7) as Ind. unfold psi_ind in Ind. simp_in Ind.
  specialize (Ind (outer_step HG HX F s a Os Hf Hd Hr) Oa). unfold PsiP in Ind. fmp Ind (wo_succ_in a s Hs).
  fobtain (w_dom0_app HG HX F s a Hd (wo_succ_in a s Hs)) as Wc HWc.
  fobtain (w_def_ex HG HX Y) as D HD.
  finst Ind Wc. fmp Ind HWc. finst Ind Y. fmp Ind HY. finst Ind D. fmp Ind HD. rename Ind into HWO.
  pose proof (w_LL_trans HG HX a Y Oa HY) as TY. pose proof (w_def_trans HG HX Y D TY HD) as HYD.
  unfold ACmat. fintro Hne. fintro Hdisj.
  fobtain (w_union0_ex HG HX x) as U HU.
  getinst Hin8 (forall_times 2 (ax_sep' ChF)). pose proof (sep_use _ 2 ChF (x .: Wc .: var) U Hin8 fb_ChF) as T. unfold ChF in T. simp_in T. fex T c Hc.
  fexists c. fall y. fintro Hy.
  fassert HyY : (y ∈' Y). { unfold Trans0 in TY. finst TY x. fmp TY Hx. finst TY y. exact (IE TY Hy). }
  fassert HyD : (Sub0 y D).
  { unfold Sub0. fall z. fintro Hz. apply (wo_sub0_use HG _ _ _ HYD).
    pose proof TY as T'. unfold Trans0 in T'. finst T' y. fmp T' HyY. finst T' z. exact (IE T' Hz). }
  pose proof Hne as H. finst H y. fmp H Hy. fex H u Hu.
  pose proof (wo_least Wc D y u HWO HyD Hu) as L. fex L m Hm.
  fexists m. fsplit; [fsplit; [exact (lst_in _ _ _ Hm)|]|].
  - pose proof Hc as H. finst H m. apply (iff_r _ _ _ H). fsplit.
    + unfold Union0 in HU. pose proof (CE2 HU) as H'. finst H' y. fmp H' Hy. finst H' m. exact (IE H' (lst_in _ _ _ Hm)).
    + fexists y. fsplit; [exact Hy|exact Hm].
  - fall z. fintro Hz. fintro Hzc. pose proof Hc as H. finst H z. pose proof (CE2 (iff_l _ _ _ H Hzc)) as H'. clear H.
    fex H' y' Hy'. fdestr Hy' Hy1 Hy2.
    apply (XM_rule _ (y ≡' y')).
    + fintro E. frew_in E (Lst Wc`[↑] $0 z`[↑]) Hy2. exact (lst_unique HG Wc D y z m HWO HyD Hy2 Hm).
    + fintro NE. fabsurd. pose proof Hdisj as H. finst H y. fmp H Hy. finst H y'. fmp H Hy1. fmp H NE.
      apply (IE H). fexists z. fsplit; [exact Hz|exact (lst_in _ _ _ Hy2)].
Qed.

(** ** The theorem *)
Section WO.
Context {G : list form} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HW : incl Ax_wo G).

Theorem wo_choice : G ⊢C ∀ (Ord0 $0 → ∀ (LL $1 $0 → ∀ ($0 ∈' $1 → ACmat $0))).
Proof. exact (wo_choice' HG (conj HR (conj HOm HW))). Qed.

End WO.
