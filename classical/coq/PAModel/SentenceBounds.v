(** A small reflected free-variable check for the concrete PA sentence. *)
From PAModel Require Import UniformSearch.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Bool Arith PeanoNat Vectors.Vector.
Unset Implicit Arguments.

Definition vector_allb {A} (p : A -> bool) :=
  fix check_args {n} (v : Vector.t A n) : bool :=
    match v with
    | Vector.nil _ => true
    | Vector.cons _ x _ xs => p x && check_args xs
    end.

Lemma vector_allb_true {A n} p (v : Vector.t A n) :
  vector_allb p v = true <-> forall x, Vector.In x v -> p x = true.
Proof.
  induction v as [|x n xs IH]; cbn.
  - split; [intros _ y H; inversion H|reflexivity].
  - rewrite Bool.andb_true_iff, IH. split.
    + intros [Hx Hxs] y H. apply Vector.In_cons_iff in H as [->|H]; auto.
    + intro H. split; [apply H; constructor|].
      intros y Hy. apply H. now constructor 2.
Qed.

Fixpoint term_boundb (k : nat) (t : term) {struct t} : bool :=
  match t with
  | var n => n <? k
  | func _ args =>
      let fix check_args {n} (args : Vector.t term n) : bool :=
        match args with
        | Vector.nil _ => true
        | Vector.cons _ x _ xs => term_boundb k x && check_args xs
        end in check_args args
  end.

Lemma term_boundb_sound k t : term_boundb k t = true -> bounded_t k t.
Proof.
  induction t as [n|f args IH] using term_ind; cbn.
  - intro H. constructor. now apply Nat.ltb_lt.
  - fold term_boundb.
    change (vector_allb (term_boundb k) args = true -> bounded_t k (func f args)).
    rewrite vector_allb_true. intro H. constructor.
    intros t Ht. apply IH; [exact Ht|]. now apply H.
Qed.

Fixpoint formula_boundb {ff} (k : nat) (phi : form ff) {struct phi} : bool :=
  match phi return bool with
  | falsity => true
  | atom _ args => vector_allb (term_boundb k) args
  | bin _ a b => formula_boundb k a && formula_boundb k b
  | quant _ a => formula_boundb (S k) a
  end.

Lemma formula_boundb_sound phi :
  forall k, formula_boundb k phi = true -> bounded k phi.
Proof.
  induction phi; intros k; cbn.
  - intros _. constructor.
  - rewrite vector_allb_true. intro H. constructor.
    intros u Hu. apply term_boundb_sound. now apply H.
  - rewrite Bool.andb_true_iff. intros [Ha Hb]. constructor; auto.
  - intro H. constructor. now apply IHphi.
Qed.

Theorem numerical_search_soundness_sentence_closed :
  closed numerical_search_soundness_sentence.
Proof.
  apply formula_boundb_sound. vm_compute. reflexivity.
Qed.

Print Assumptions numerical_search_soundness_sentence_closed.
