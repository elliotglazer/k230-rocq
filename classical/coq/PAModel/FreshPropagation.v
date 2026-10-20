(** Freshness passes to children along internally coded formula paths.
    The prepend construction follows the existing InternalPaths argument,
    using beta concatenation with model-valued lengths. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  BetaExtension BetaPacking Pairing CodeExpressions NumericalProofs
  CodeDescent CodeTags FreshNames.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import setoid_ring.Ring.
Unset Implicit Arguments.

Section Propagation.
Variable M : Model.
Local Notation D := (carrier M).
Local Notation O := (zeroM M).
Local Notation S := (succM M).
Local Infix "+" := (addM M).
Add Ring fresh_propagation_ring : (model_semiring M).

Theorem formula_reaches_step f a g :
  formula_edge M f a -> formula_reaches M a g -> formula_reaches M f g.
Proof.
  intros Hfa [b [c [n [Ha [Hg Hp]]]]].
  destruct (beta_concatenate M f f (S O) b c (S n)) as [b' [c' [Hl Hr]]].
  exists b',c',(S n). split.
  - apply Hl; [apply coding_zero_lt_succ|apply beta_singleton].
  - split.
    + pose proof (Hr n g (coding_lt_succ M n) Hg) as H.
      rewrite (Arithmetic.add_succ M O n), (Arithmetic.add_zero M n) in H. exact H.
    + intros i x y Hi Hx Hy.
      destruct (@Peano.zero_or_succ D (raw_interpretation M)
        (fun ax H rho => axioms M ax rho H) i) as [-> | [j ->]].
      * assert (Ex : x=f).
        { eapply beta_unique; [exact Hx|apply Hl; [apply coding_zero_lt_succ|apply beta_singleton]]. }
        assert (Ey : y=a).
        { eapply beta_unique; [exact Hy|].
          pose proof (Hr O a (coding_zero_lt_succ M n) Ha) as H.
          replace (S O+O) with (S O) in H by ring. exact H. }
        now subst x y.
      * assert (Hjn : coding_lt M j n) by (apply coding_lt_succ_cancel;exact Hi).
        assert (Hsj : coding_lt M (S j) (S n)) by exact Hi.
        destruct (beta_total M b c j) as [x' Hx'].
        destruct (beta_total M b c (S j)) as [y' Hy'].
        assert (Ex : x=x').
        { eapply beta_unique; [exact Hx|].
          pose proof (Hr j x' (proj2 (coding_lt_succ_cases M j n) (or_introl Hjn)) Hx') as H.
          rewrite (Arithmetic.add_succ M O j), (Arithmetic.add_zero M j) in H. exact H. }
        assert (Ey : y=y').
        { eapply beta_unique; [exact Hy|].
          pose proof (Hr (S j) y' Hsj Hy') as H.
          rewrite (Arithmetic.add_succ M O (S j)), (Arithmetic.add_zero M (S j)) in H. exact H. }
        subst x y. exact (Hp j x' y' Hjn Hx' Hy').
Qed.

Theorem formula_mentions_step f a v :
  formula_edge M f a -> formula_mentions M a v -> formula_mentions M f v.
Proof.
  intros He [g [Hg Hv]]. exists g. split; [eapply formula_reaches_step;eassumption|exact Hv].
Qed.

Theorem formula_fresh_child f a k :
  formula_fresh M f k -> formula_edge M f a -> formula_fresh M a k.
Proof.
  intros Hfresh Hedge v Hv. apply Hfresh. eapply formula_mentions_step; eassumption.
Qed.

Lemma formula_node_is_mentioned f v : node_mentions M f v -> formula_mentions M f v.
Proof. intro H. exists f. split; [apply formula_reaches_self|exact H]. Qed.

Theorem formula_fresh_membership a b f k :
  membership_graph M a b f -> formula_fresh M f k -> a<>k /\ b<>k.
Proof.
  intros Hm Hf. split; apply Hf; apply formula_node_is_mentioned; exists a,b;
    left; split; [now left|now left|now left|now right].
Qed.

Theorem formula_fresh_equality a b f k :
  equality_graph M a b f -> formula_fresh M f k -> a<>k /\ b<>k.
Proof.
  intros Hm Hf. split; apply Hf; apply formula_node_is_mentioned; exists a,b;
    left; split; [now right|now left|now right|now right].
Qed.

Theorem formula_fresh_universal_tagged a b f k :
  tagged_pair_graph M 2 a b f -> formula_fresh M f k -> a<>k /\ formula_fresh M b k.
Proof.
  intros Hg Hf. split.
  - apply Hf. apply formula_node_is_mentioned. exists a,b. right. auto.
  - apply (formula_fresh_child f b k Hf). exists a,b. right. auto.
Qed.

Theorem formula_fresh_universal a b f k :
  universal_graph M a b f -> formula_fresh M f k -> a<>k /\ formula_fresh M b k.
Proof. intro H. apply formula_fresh_universal_tagged. now apply universal_graph_tagged. Qed.

Theorem formula_fresh_implication_tagged a b f k :
  f<>O -> tagged_pair_graph M 0 a b f -> formula_fresh M f k ->
  formula_fresh M a k /\ formula_fresh M b k.
Proof.
  intros Hnz Hg Hf. split.
  - apply (formula_fresh_child f a k Hf). exists a,b. left. auto.
  - apply (formula_fresh_child f b k Hf). exists a,b. left. auto.
Qed.

Theorem formula_fresh_implication a b f k :
  f<>O -> implication_graph M a b f -> formula_fresh M f k ->
  formula_fresh M a k /\ formula_fresh M b k.
Proof. intros Hnz H. apply formula_fresh_implication_tagged; [exact Hnz|now apply implication_graph_tagged]. Qed.

End Propagation.
