(** * Z_base: Delta_0 primitives for the constructible hierarchy.

    Every predicate here is (after unfolding) a syntactic Delta_0 formula when its arguments are
    variables ([D0] of Z_rel), so the predicates built from them stay Sigma and are upward
    absolute.  Each has a substitution lemma in [fsub].  Equivalences with the predicates of
    Std_setbase (library-style, not syntactically Delta_0) give access to that toolkit. *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_setinf.
From OldZFC Require Import Z_rel.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition Sing0 (x s : term) : form := x ∈' s ∧ ∀ ($0 ∈' s`[↑] → $0 ≡' x`[↑]).
Definition Pair0 (x y p : term) : form := x ∈' p ∧ y ∈' p ∧ ∀ ($0 ∈' p`[↑] → $0 ≡' x`[↑] ∨ $0 ≡' y`[↑]).
(** ordered pair p = {{x},{x,y}} *)
Definition OP0 (x y p : term) : form :=
  (∃ ($0 ∈' p`[↑] ∧ Sing0 x`[↑] $0)) ∧ (∃ ($0 ∈' p`[↑] ∧ Pair0 x`[↑] y`[↑] $0)) ∧
  ∀ ($0 ∈' p`[↑] → Sing0 x`[↑] $0 ∨ Pair0 x`[↑] y`[↑] $0).
Definition Emp0 (x : term) : form := ∀ ($0 ∈' x`[↑] → ⊥).
Definition Sub0 (x y : term) : form := ∀ ($0 ∈' x`[↑] → $0 ∈' y`[↑]).
Definition Trans0 (x : term) : form := ∀ ($0 ∈' x`[↑] → ∀ ($0 ∈' $1 → $0 ∈' x`[↑]`[↑])).
Definition Ord0 (x : term) : form := Trans0 x ∧ ∀ ($0 ∈' x`[↑] → Trans0 $0).
(** s = x ∪ {x} *)
Definition Succ0 (x s : term) : form :=
  x ∈' s ∧ Sub0 x s ∧ ∀ ($0 ∈' s`[↑] → $0 ∈' x`[↑] ∨ $0 ≡' x`[↑]).
Definition Lim0 (x : term) : form :=
  Ord0 x ∧ (∃ ($0 ∈' x`[↑] ∧ $0 ≡' $0)) ∧ ∀ ($0 ∈' x`[↑] → ∃ ($0 ∈' x`[↑]`[↑] ∧ $1 ∈' $0)).
(** w = ω: the least nonzero limit ordinal *)
Definition Om0 (w : term) : form :=
  Lim0 w ∧ ∀ ($0 ∈' w`[↑] → Emp0 $0 ∨ ∃ ($0 ∈' $1 ∧ Succ0 $0 $1)).
(** u = ⋃x *)
Definition Union0 (x u : term) : form :=
  (∀ ($0 ∈' u`[↑] → ∃ ($0 ∈' x`[↑]`[↑] ∧ $1 ∈' $0))) ∧ ∀ ($0 ∈' x`[↑] → ∀ ($0 ∈' $1 → $0 ∈' u`[↑]`[↑])).
(** (u, v) ∈ f *)
Definition App0 (f u v : term) : form := ∃ ($0 ∈' f`[↑] ∧ OP0 u`[↑] v`[↑] $0).

(** [PairsAll f B]: for every ordered pair (u, v) ∈ f, B holds, where in B the variable $1 is u,
    $0 is v and $(k+2) is the outer variable $k.  Bounded: u ∈ s ∈ p, v ∈ s' ∈ p. *)
Definition PairsAll (f : term) (B : form) : form :=
  ∀ ($0 ∈' f`[↑] → ∀ ($0 ∈' $1 → ∀ ($0 ∈' $1 → ∀ ($0 ∈' $3 → ∀ ($0 ∈' $1 →
    OP0 $2 $0 $4 → B[$0 .: $2 .: (fun k => $(k + 5))]))))).
(** every element of f is an ordered pair *)
Definition IsRel0 (f : term) : form :=
  ∀ ($0 ∈' f`[↑] → ∃ ($0 ∈' $1 ∧ ∃ ($0 ∈' $1 ∧ ∃ ($0 ∈' $3 ∧ ∃ ($0 ∈' $1 ∧ OP0 $2 $0 $4))))).
(** f is a function (a set of ordered pairs, single-valued) *)
Definition Fun0 (f : term) : form :=
  IsRel0 f ∧ PairsAll f (PairsAll f`[↑]`[↑] ($3 ≡' $1 → $2 ≡' $0)).
(** dom f = d *)
Definition Dom0 (f d : term) : form :=
  (∀ ($0 ∈' d`[↑] → ∃ ($0 ∈' f`[↑]`[↑] ∧ ∃ ($0 ∈' $1 ∧ ∃ ($0 ∈' $1 ∧ OP0 $3 $0 $2))))) ∧
  PairsAll f ($1 ∈' d`[↑]`[↑]).

#[global] Arguments Sing0 : simpl never.
#[global] Arguments Pair0 : simpl never.
#[global] Arguments OP0 : simpl never.
#[global] Arguments Emp0 : simpl never.
#[global] Arguments Sub0 : simpl never.
#[global] Arguments Trans0 : simpl never.
#[global] Arguments Ord0 : simpl never.
#[global] Arguments Succ0 : simpl never.
#[global] Arguments Lim0 : simpl never.
#[global] Arguments Om0 : simpl never.
#[global] Arguments Union0 : simpl never.
#[global] Arguments App0 : simpl never.
#[global] Arguments PairsAll : simpl never.
#[global] Arguments IsRel0 : simpl never.
#[global] Arguments Fun0 : simpl never.
#[global] Arguments Dom0 : simpl never.

Lemma Sing0_subst x s sg : (Sing0 x s)[sg] = Sing0 x`[sg] s`[sg].
Proof. psubst Sing0. Qed.
Lemma Pair0_subst x y p sg : (Pair0 x y p)[sg] = Pair0 x`[sg] y`[sg] p`[sg].
Proof. psubst Pair0. Qed.
#[global] Hint Rewrite Sing0_subst Pair0_subst : fsub.
Lemma OP0_subst x y p sg : (OP0 x y p)[sg] = OP0 x`[sg] y`[sg] p`[sg].
Proof. psubst OP0. Qed.
Lemma Emp0_subst x sg : (Emp0 x)[sg] = Emp0 x`[sg].
Proof. psubst Emp0. Qed.
Lemma Sub0_subst x y sg : (Sub0 x y)[sg] = Sub0 x`[sg] y`[sg].
Proof. psubst Sub0. Qed.
Lemma Trans0_subst x sg : (Trans0 x)[sg] = Trans0 x`[sg].
Proof. psubst Trans0. Qed.
#[global] Hint Rewrite OP0_subst Emp0_subst Sub0_subst Trans0_subst : fsub.
Lemma Ord0_subst x sg : (Ord0 x)[sg] = Ord0 x`[sg].
Proof. psubst Ord0. Qed.
Lemma Succ0_subst x s sg : (Succ0 x s)[sg] = Succ0 x`[sg] s`[sg].
Proof. psubst Succ0. Qed.
#[global] Hint Rewrite Ord0_subst Succ0_subst : fsub.
Lemma Lim0_subst x sg : (Lim0 x)[sg] = Lim0 x`[sg].
Proof. psubst Lim0. Qed.
#[global] Hint Rewrite Lim0_subst : fsub.
Lemma Om0_subst x sg : (Om0 x)[sg] = Om0 x`[sg].
Proof. psubst Om0. Qed.
Lemma Union0_subst x u sg : (Union0 x u)[sg] = Union0 x`[sg] u`[sg].
Proof. psubst Union0. Qed.
Lemma App0_subst f u v sg : (App0 f u v)[sg] = App0 f`[sg] u`[sg] v`[sg].
Proof. psubst App0. Qed.
#[global] Hint Rewrite Om0_subst Union0_subst App0_subst : fsub.

Lemma PairsAll_subst f B sg : (PairsAll f B)[sg] = PairsAll f`[sg] (B[up (up sg)]).
Proof.
  unfold PairsAll. cbn. autorewrite with fsub. cbn. fix_up. rewrite !subst_comp.
  match goal with |- _ = ?R => match R with context [B[?s2]] => erewrite (@subst_ext _ _ _ _ B _ s2) end end;
    [reflexivity|]. intros [|[|k]]; cbn; try reflexivity.
  replace (k + 5) with (S (S (S (S (S k))))) by lia. cbn. unfold funcomp.
  rewrite !subst_term_comp. apply subst_term_ext. intros n. cbn. f_equal. lia.
Qed.
#[global] Hint Rewrite PairsAll_subst : fsub.
Lemma IsRel0_subst f sg : (IsRel0 f)[sg] = IsRel0 f`[sg].
Proof. psubst IsRel0. Qed.
#[global] Hint Rewrite IsRel0_subst : fsub.
Lemma Fun0_subst f sg : (Fun0 f)[sg] = Fun0 f`[sg].
Proof. unfold Fun0. cbn. autorewrite with fsub. cbn. now autorewrite with fsub. Qed.
Lemma Dom0_subst f d sg : (Dom0 f d)[sg] = Dom0 f`[sg] d`[sg].
Proof. unfold Dom0. cbn. autorewrite with fsub. cbn. autorewrite with fsub. fix_up. reflexivity. Qed.
#[global] Hint Rewrite Fun0_subst Dom0_subst : fsub.

(** Delta_0 checks *)
Goal D0 (OP0 $0 $1 $2). Proof. unfold OP0, Sing0, Pair0. d0solve. Qed.
Goal D0 (Fun0 $0). Proof. unfold Fun0, IsRel0, PairsAll, OP0, Sing0, Pair0. d0solve. Qed.
Goal D0 (Dom0 $0 $1). Proof. unfold Dom0, PairsAll, OP0, Sing0, Pair0. d0solve. Qed.
Goal D0 (Om0 $0). Proof. unfold Om0, Lim0, Ord0, Trans0, Emp0, Succ0, Sub0. d0solve. Qed.
Goal D0 (Union0 $0 $1). Proof. unfold Union0. d0solve. Qed.
Goal D0 (App0 $0 $1 $2). Proof. unfold App0, OP0, Sing0, Pair0. d0solve. Qed.
