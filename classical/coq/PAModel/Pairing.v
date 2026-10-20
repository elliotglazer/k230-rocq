(** Cantor pairing as an arithmetic graph on every PA model.  All quantified
    arithmetic inputs below range over the model, including nonstandard ones. *)
From PAModel Require Import Model Arithmetic FiniteCoding.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import setoid_ring.Ring.
Unset Implicit Arguments.

Definition twoM M := succM M (succM M (zeroM M)).

Definition triangular_graph (M : Model) (x t : carrier M) : Prop :=
  mulM M (twoM M) t = mulM M x (succM M x).

Definition pair_graph (M : Model) (a b z : carrier M) : Prop :=
  mulM M (twoM M) z =
    addM M (mulM M (addM M a b) (succM M (addM M a b)))
      (mulM M (twoM M) b).

Definition pair_formula (a b z : term) : form :=
  (num 2 ⊗ z) == (((a ⊕ b) ⊗ σ (a ⊕ b)) ⊕ (num 2 ⊗ b)).

Lemma pair_formula_correct (M : Model) rho a b z :
  holds M rho (pair_formula a b z) <->
    pair_graph M (evalM M rho a) (evalM M rho b) (evalM M rho z).
Proof. reflexivity. Qed.

Definition triangular_exists_formula : form :=
  ∃ (num 2 ⊗ $0) == ($1 ⊗ σ $1).

Lemma triangular_exists_formula_correct (M : Model) rho x :
  holds M (x .: rho) triangular_exists_formula <->
    exists t, triangular_graph M x t.
Proof. reflexivity. Qed.

Section Pairing.
Variable M : Model.
Local Notation D := (carrier M).
Local Notation O := (zeroM M).
Local Notation S := (succM M).
Local Notation add := (addM M).
Local Notation mul := (mulM M).
Local Notation two := (twoM M).
Add Ring pairing_ring : (model_semiring M).

Lemma consecutive_product_even x : exists t, triangular_graph M x t.
Proof.
  apply (definable_induction M (fun x => exists t, triangular_graph M x t)).
  - exists triangular_exists_formula, (fun _ => O).
    intro n. symmetry. apply triangular_exists_formula_correct.
  - exists O. unfold triangular_graph. ring.
  - intros n [t Ht]. exists (add t (S n)).
    unfold triangular_graph in *.
    replace (mul two (add t (S n))) with
      (add (mul two t) (mul two (S n))) by ring.
    rewrite Ht. symmetry. apply consecutive_product_step.
Qed.

Lemma positive_mul_cancel q x y :
  coding_lt M O q -> mul x q = mul y q -> x = y.
Proof.
  intros Hq Hxy.
  assert (E : add O (mul x q) = add O (mul y q)) by now rewrite Hxy.
  exact (proj1 (@Peano.iFac_unique D (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) q x O y O Hq Hq E)).
Qed.

Lemma double_cancel x y : mul two x = mul two y -> x = y.
Proof.
  rewrite (mul_comm M two x), (mul_comm M two y).
  apply positive_mul_cancel. apply coding_zero_lt_succ.
Qed.

Lemma triangular_unique x t u :
  triangular_graph M x t -> triangular_graph M x u -> t = u.
Proof. unfold triangular_graph. intros Ht Hu. apply double_cancel. congruence. Qed.

Lemma pair_total a b : exists z, pair_graph M a b z.
Proof.
  destruct (consecutive_product_even (add a b)) as [t Ht].
  exists (add t b). unfold pair_graph, triangular_graph in *.
  replace (mul two (add t b)) with (add (mul two t) (mul two b)) by ring.
  now rewrite Ht.
Qed.

Lemma pair_functional a b z z' :
  pair_graph M a b z -> pair_graph M a b z' -> z = z'.
Proof. unfold pair_graph. intros Hz Hz'. apply double_cancel. congruence. Qed.

Lemma pair_zero : pair_graph M O O O.
Proof. unfold pair_graph. ring. Qed.

Lemma pair_successor_left a b z :
  pair_graph M (S a) b z -> pair_graph M a (S b) (S z).
Proof.
  unfold pair_graph. intro H.
  rewrite (succ_as_add M a), (succ_as_add M b), (succ_as_add M z) in *.
  rewrite (succ_as_add M (add a (add b (S O)))) in *.
  rewrite (succ_as_add M (add (add a (S O)) b)) in *.
  unfold twoM in *.
  rewrite (succ_as_add M (S O)) in *.
  replace (mul (add (S O) (S O)) (add z (S O))) with
    (add (mul (add (S O) (S O)) z) (add (S O) (S O))) by ring.
  rewrite H. ring.
Qed.

Lemma pair_successor_diagonal b z :
  pair_graph M O b z -> pair_graph M (S b) O (S z).
Proof.
  unfold pair_graph. intro H.
  rewrite (Arithmetic.add_zero M b) in H.
  rewrite (Arithmetic.add_comm M (S b) O), (Arithmetic.add_zero M (S b)).
  rewrite (succ_as_add M (S b)), (succ_as_add M b), (succ_as_add M z) in *.
  unfold twoM in *.
  rewrite (succ_as_add M (S O)) in *.
  replace (mul (add (S O) (S O)) (add z (S O))) with
    (add (mul (add (S O) (S O)) z) (add (S O) (S O))) by ring.
  rewrite H. ring.
Qed.

Lemma pair_surjective z : exists a b, pair_graph M a b z.
Proof.
  apply (definable_induction M (fun z => exists a b, pair_graph M a b z)).
  - exists (∃∃ (num 2 ⊗ $2) ==
      ((($1 ⊕ $0) ⊗ σ ($1 ⊕ $0)) ⊕ (num 2 ⊗ $0))), (fun _ => O).
    intro x. reflexivity.
  - exists O, O. apply pair_zero.
  - intros x [a [b H]].
    destruct (@Peano.zero_or_succ D (raw_interpretation M)
      (fun ax H rho => axioms M ax rho H) a) as [-> | [a' ->]].
    + exists (S b), O. now apply pair_successor_diagonal.
    + exists a', (S b). now apply pair_successor_left.
Qed.

Lemma pair_at_zero a b : pair_graph M a b O -> a = O /\ b = O.
Proof.
  unfold pair_graph. intro H.
  assert (Z : mul two O = O) by ring.
  rewrite Z in H. symmetry in H.
  destruct (@Peano.sum_is_zero D (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) _ _ H) as [Hprod Hb].
  assert (B : b = O) by (apply double_cancel; now rewrite Hb, Z).
  subst b. split; [|reflexivity].
  rewrite (Arithmetic.add_comm M a O), (Arithmetic.add_zero M a) in Hprod.
  apply (positive_mul_cancel (S a)); [apply coding_zero_lt_succ|].
  now rewrite Hprod, (mul_zero M (S a)).
Qed.

Definition pair_walk a b c d : Prop :=
  (a = O /\ c = S b /\ d = O) \/
  exists u, a = S u /\ c = u /\ d = S b.

Lemma pair_walk_functional a b c d c' d' :
  pair_walk a b c d -> pair_walk a b c' d' -> c = c' /\ d = d'.
Proof.
  intros [[Ha [Hc Hd]]|[u [Ha [Hc Hd]]]]
         [[Ha' [Hc' Hd']]|[v [Ha' [Hc' Hd']]]].
  - split; congruence.
  - exfalso. apply (zero_ne_succ M v). congruence.
  - exfalso. apply (zero_ne_succ M u). congruence.
  - assert (u = v) by (apply (succ_injective M); congruence). split; congruence.
Qed.

Lemma pair_predecessor a b z :
  pair_graph M a b (S z) ->
  exists a' b', pair_graph M a' b' z /\ pair_walk a' b' a b.
Proof.
  intro H.
  destruct (@Peano.zero_or_succ D (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) b) as [->|[b' ->]].
  - destruct (@Peano.zero_or_succ D (raw_interpretation M)
      (fun ax H rho => axioms M ax rho H) a) as [->|[a' ->]].
    + exfalso. apply (zero_ne_succ M z).
      symmetry. exact (pair_functional O O (S z) O H pair_zero).
    + destruct (pair_total O a') as [q Hq].
      pose proof (pair_successor_diagonal a' q Hq) as Hq'.
      assert (E : q = z).
      { apply (succ_injective M). exact (pair_functional (S a') O (S q) (S z) Hq' H). }
      subst q. exists O, a'. split; [exact Hq|left; auto].
  - destruct (pair_total (S a) b') as [q Hq].
    pose proof (pair_successor_left a b' q Hq) as Hq'.
    assert (E : q = z).
    { apply (succ_injective M). exact (pair_functional a (S b') (S q) (S z) Hq' H). }
    subst q. exists (S a), b'. split; [exact Hq|right; exists a; auto].
Qed.

Lemma pair_injective z : forall a b a' b',
  pair_graph M a b z -> pair_graph M a' b' z -> a = a' /\ b = b'.
Proof.
  apply (definable_induction M (fun z => forall a b a' b',
    pair_graph M a b z -> pair_graph M a' b' z -> a = a' /\ b = b')).
  - exists (∀∀∀∀ (pair_formula $3 $2 $4 →
      pair_formula $1 $0 $4 → ($3 == $1 ∧ $2 == $0))), (fun _ => O).
    intro x. reflexivity.
  - intros a b a' b' H H'.
    destruct (pair_at_zero a b H), (pair_at_zero a' b' H'). split; congruence.
  - intros n IH a b a' b' H H'.
    destruct (pair_predecessor a b n H) as [u [v [Huv Hw]]].
    destruct (pair_predecessor a' b' n H') as [u' [v' [Huv' Hw']]].
    destruct (IH u v u' v' Huv Huv') as [E E']. subst u' v'.
    exact (pair_walk_functional u v a b a' b' Hw Hw').
Qed.

End Pairing.

Definition pair3 : form := pair_formula $2 $1 $0.

Lemma pair3_correct (M : Model) rho a b z :
  holds M (z .: b .: a .: rho) pair3 <-> pair_graph M a b z.
Proof. reflexivity. Qed.

Lemma pair_total_sentence (M : Model) rho :
  holds M rho (∀∀∃ pair3).
Proof. change (forall a b, exists z, pair_graph M a b z). exact (pair_total M). Qed.
