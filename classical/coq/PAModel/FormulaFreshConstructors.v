(** Introduction rules for the existing full named-formula freshness
    predicate, using its internally finite reachability definition. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  CodeExpressions NumericalProofs CodeDescent CodeTags FreshNames
  FreshPropagation NamedBinderConstructors FormulaReachability.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Lemma formula_fresh_or_root_definable M f y :
  Definable1 M (fun g => g=f \/ formula_fresh M g y).
Proof.
  exists (($0 == $1) ∨ formula_fresh_formula $0 $2),
    (f .: y .: (fun _ => zeroM M)).
  intro g. rewrite holds_or, fresh_holds_eq, formula_fresh_formula_correct. reflexivity.
Qed.

Theorem formula_fresh_intro M f y :
  (forall v, node_mentions M f v -> v<>y) ->
  (forall g, formula_edge M f g -> formula_fresh M g y) -> formula_fresh M f y.
Proof.
  intros Hroot Hchildren v [g [Hreach Hmention]] E. subst v.
  assert (Hg : g=f \/ formula_fresh M g y).
  { eapply (formula_reaches_induction M (fun g => g=f \/ formula_fresh M g y)) with (f:=f).
    - apply formula_fresh_or_root_definable.
    - intros a d [-> | Ha] Hedge.
      + right. exact (Hchildren d Hedge).
      + right. exact (formula_fresh_child M a d y Ha Hedge).
    - now left.
    - exact Hreach. }
  destruct Hg as [-> | Hg].
  - exact (Hroot y Hmention eq_refl).
  - apply (Hg y); [|reflexivity]. exists g. split; [apply formula_reaches_self|exact Hmention].
Qed.

Lemma positive_tag_not_zero M tag a b : tag<>0 ->
  ~tagged_pair_graph M tag a b (zeroM M).
Proof.
  intros Htag H. exact (coding_not_lt_zero M a
    (proj1 (tagged_pair_positive_descent M a b (zeroM M) tag Htag H))).
Qed.

Theorem formula_fresh_zero M y : formula_fresh M (zeroM M) y.
Proof.
  apply formula_fresh_intro.
  - intros v [a [b [[[H | H] Hv] | [H Hv]]]] E.
    + exact (positive_tag_not_zero M 1 a b ltac:(lia) H).
    + exact (positive_tag_not_zero M 3 a b ltac:(lia) H).
    + exact (positive_tag_not_zero M 2 a b ltac:(lia) H).
  - intros g Hg. exfalso. exact (formula_zero_no_edge M g Hg).
Qed.

Lemma node_mentions_atom M tag a b f v :
  tag=1 \/ tag=3 -> tagged_pair_graph M tag a b f -> node_mentions M f v -> v=a \/ v=b.
Proof.
  intros Htag Hf [c [d [[[H | H] Hv] | [H Hv]]]];
    assert (Ht : tag<4) by (destruct Htag as [-> | ->]; lia).
  - destruct (tagged_pair_decode_unique M tag 1 a b c d f Ht ltac:(lia) Hf H)
      as [_ [Ec Ed]]. now subst c d.
  - destruct (tagged_pair_decode_unique M tag 3 a b c d f Ht ltac:(lia) Hf H)
      as [_ [Ec Ed]]. now subst c d.
  - destruct (tagged_pair_decode_unique M tag 2 a b c d f Ht ltac:(lia) Hf H)
      as [E _]. destruct Htag as [-> | ->]; discriminate E.
Qed.

Theorem formula_fresh_atom M tag a b f y :
  tag=1 \/ tag=3 -> tagged_pair_graph M tag a b f -> a<>y -> b<>y -> formula_fresh M f y.
Proof.
  intros Htag Hf Ha Hb. apply formula_fresh_intro.
  - intros v Hv. destruct (node_mentions_atom M tag a b f v Htag Hf Hv) as [-> | ->]; assumption.
  - intros g Hg. exfalso. exact (named_atom_no_edge M tag a b f g Htag Hf Hg).
Qed.

Theorem formula_fresh_membership_intro M a b f y :
  membership_graph M a b f -> a<>y -> b<>y -> formula_fresh M f y.
Proof. intro H. exact (formula_fresh_atom M 1 a b f y (or_introl eq_refl) H). Qed.

Theorem formula_fresh_equality_intro M a b f y :
  equality_graph M a b f -> a<>y -> b<>y -> formula_fresh M f y.
Proof. intro H. exact (formula_fresh_atom M 3 a b f y (or_intror eq_refl) H). Qed.

Theorem formula_fresh_implication_tagged_intro M a b f y :
  tagged_pair_graph M 0 a b f -> formula_fresh M a y -> formula_fresh M b y -> formula_fresh M f y.
Proof.
  intros Hf Ha Hb. apply formula_fresh_intro.
  - intros v [c [d [[[H | H] Hv] | [H Hv]]]] E.
    + destruct (tagged_pair_decode_unique M 0 1 a b c d f ltac:(lia) ltac:(lia) Hf H)
        as [Htag _]. discriminate Htag.
    + destruct (tagged_pair_decode_unique M 0 3 a b c d f ltac:(lia) ltac:(lia) Hf H)
        as [Htag _]. discriminate Htag.
    + destruct (tagged_pair_decode_unique M 0 2 a b c d f ltac:(lia) ltac:(lia) Hf H)
        as [Htag _]. discriminate Htag.
  - intros g [c [d [[Hnz [Hg [Eg | Eg]]] | [Hg Eg]]]].
    + destruct (tagged_pair_decode_unique M 0 0 a b c d f ltac:(lia) ltac:(lia) Hf Hg)
        as [_ [Ec Ed]]. now subst c d g.
    + destruct (tagged_pair_decode_unique M 0 0 a b c d f ltac:(lia) ltac:(lia) Hf Hg)
        as [_ [Ec Ed]]. now subst c d g.
    + destruct (tagged_pair_decode_unique M 0 2 a b c d f ltac:(lia) ltac:(lia) Hf Hg)
        as [E _]. discriminate E.
Qed.

Theorem formula_fresh_implication_intro M a b f y :
  implication_graph M a b f -> formula_fresh M a y -> formula_fresh M b y -> formula_fresh M f y.
Proof. intro H. apply formula_fresh_implication_tagged_intro. now apply implication_graph_tagged. Qed.

Theorem formula_fresh_universal_tagged_intro M a b f y :
  tagged_pair_graph M 2 a b f -> a<>y -> formula_fresh M b y -> formula_fresh M f y.
Proof.
  intros Hf Ha Hb. apply formula_fresh_intro.
  - intros v [c [d [[[H | H] Hv] | [H Hv]]]].
    + destruct (tagged_pair_decode_unique M 2 1 a b c d f ltac:(lia) ltac:(lia) Hf H)
        as [E _]. discriminate E.
    + destruct (tagged_pair_decode_unique M 2 3 a b c d f ltac:(lia) ltac:(lia) Hf H)
        as [E _]. discriminate E.
    + destruct (tagged_pair_decode_unique M 2 2 a b c d f ltac:(lia) ltac:(lia) Hf H)
        as [_ [Ec Ed]]. now subst c d v.
  - intros g [c [d [[Hnz [Hg Eg]] | [Hg Eg]]]].
    + destruct (tagged_pair_decode_unique M 2 0 a b c d f ltac:(lia) ltac:(lia) Hf Hg)
        as [E _]. discriminate E.
    + destruct (tagged_pair_decode_unique M 2 2 a b c d f ltac:(lia) ltac:(lia) Hf Hg)
        as [_ [Ec Ed]]. now subst c d g.
Qed.

Theorem formula_fresh_universal_intro M a b f y :
  universal_graph M a b f -> a<>y -> formula_fresh M b y -> formula_fresh M f y.
Proof. intro H. apply formula_fresh_universal_tagged_intro. now apply universal_graph_tagged. Qed.

Print Assumptions formula_fresh_intro.
Print Assumptions formula_fresh_zero.
Print Assumptions formula_fresh_membership_intro.
Print Assumptions formula_fresh_equality_intro.
Print Assumptions formula_fresh_implication_intro.
Print Assumptions formula_fresh_universal_intro.
