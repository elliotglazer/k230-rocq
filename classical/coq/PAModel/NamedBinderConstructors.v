(** Constructor introduction rules for the original reachability-based
    named_binder_absent predicate. Free occurrences are unrestricted. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  CodeExpressions NumericalProofs CodeDescent CodeTags FreshNames
  FreshPropagation NamedBinderFresh FormulaReachability.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Lemma binder_absent_or_root_definable M f y :
  Definable1 M (fun g => g=f \/ named_binder_absent M g y).
Proof.
  exists (($0 == $1) ∨ named_binder_absent_formula $0 $2),
    (f .: y .: (fun _ => zeroM M)).
  intro g. rewrite holds_or, fresh_holds_eq, named_binder_absent_formula_correct.
  reflexivity.
Qed.

Theorem named_binder_absent_intro M f y :
  (forall b, ~tagged_pair_graph M 2 y b f) ->
  (forall g, formula_edge M f g -> named_binder_absent M g y) ->
  named_binder_absent M f y.
Proof.
  intros Hroot Hchildren g b Hreach Hbind.
  assert (Hg : g=f \/ named_binder_absent M g y).
  { eapply (formula_reaches_induction M (fun g => g=f \/ named_binder_absent M g y)) with (f:=f).
    - apply binder_absent_or_root_definable.
    - intros a d [-> | Ha] Hedge.
      + right. exact (Hchildren d Hedge).
      + right. exact (named_binder_absent_child M a d y Hedge Ha).
    - now left.
    - exact Hreach. }
  destruct Hg as [-> | Hg].
  - exact (Hroot b Hbind).
  - exact (Hg g b (formula_reaches_self M g) Hbind).
Qed.

Lemma zero_has_no_binder M y b : ~tagged_pair_graph M 2 y b (zeroM M).
Proof.
  intro H. pose proof (proj1 (tagged_pair_positive_descent M y b (zeroM M) 2 ltac:(lia) H)) as Hy.
  exact (coding_not_lt_zero M y Hy).
Qed.

Lemma formula_zero_no_edge M g : ~formula_edge M (zeroM M) g.
Proof.
  intros [a [b [[Hnz _] | [Hg _]]]].
  - exact (Hnz eq_refl).
  - exact (zero_has_no_binder M a b Hg).
Qed.

Theorem named_binder_absent_zero M y : named_binder_absent M (zeroM M) y.
Proof.
  apply named_binder_absent_intro.
  - apply zero_has_no_binder.
  - intros g Hg. exfalso. exact (formula_zero_no_edge M g Hg).
Qed.

Lemma named_atom_no_edge M tag a b f g :
  tag=1 \/ tag=3 -> tagged_pair_graph M tag a b f -> ~formula_edge M f g.
Proof.
  intros Htag Hf [c [d [[Hnz [Hg He]] | [Hg He]]]].
  - assert (Ht : tag<4) by (destruct Htag as [-> | ->]; lia).
    destruct (tagged_pair_decode_unique M tag 0 a b c d f Ht ltac:(lia) Hf Hg)
      as [E _]. destruct Htag as [-> | ->]; discriminate E.
  - assert (Ht : tag<4) by (destruct Htag as [-> | ->]; lia).
    destruct (tagged_pair_decode_unique M tag 2 a b c d f Ht ltac:(lia) Hf Hg)
      as [E _]. destruct Htag as [-> | ->]; discriminate E.
Qed.

Theorem named_binder_absent_atom M tag a b f y :
  tag=1 \/ tag=3 -> tagged_pair_graph M tag a b f -> named_binder_absent M f y.
Proof.
  intros Htag Hf. apply named_binder_absent_intro.
  - intros d Hd. assert (Ht : tag<4) by (destruct Htag as [-> | ->]; lia).
    destruct (tagged_pair_decode_unique M tag 2 a b y d f Ht ltac:(lia) Hf Hd)
      as [E _]. destruct Htag as [-> | ->]; discriminate E.
  - intros g Hg. exfalso. exact (named_atom_no_edge M tag a b f g Htag Hf Hg).
Qed.

Theorem named_binder_absent_membership M a b f y :
  membership_graph M a b f -> named_binder_absent M f y.
Proof. intro H. exact (named_binder_absent_atom M 1 a b f y (or_introl eq_refl) H). Qed.

Theorem named_binder_absent_equality M a b f y :
  equality_graph M a b f -> named_binder_absent M f y.
Proof. intro H. exact (named_binder_absent_atom M 3 a b f y (or_intror eq_refl) H). Qed.

Theorem named_binder_absent_implication_tagged M a b f y :
  tagged_pair_graph M 0 a b f ->
  named_binder_absent M a y -> named_binder_absent M b y -> named_binder_absent M f y.
Proof.
  intros Hf Ha Hb. apply named_binder_absent_intro.
  - intros d Hd. destruct (tagged_pair_decode_unique M 0 2 a b y d f ltac:(lia) ltac:(lia) Hf Hd)
      as [E _]. discriminate E.
  - intros g [c [d [[Hnz [Hg [Eg | Eg]]] | [Hg Eg]]]].
    + destruct (tagged_pair_decode_unique M 0 0 a b c d f ltac:(lia) ltac:(lia) Hf Hg)
        as [_ [Ec Ed]]. now subst c d g.
    + destruct (tagged_pair_decode_unique M 0 0 a b c d f ltac:(lia) ltac:(lia) Hf Hg)
        as [_ [Ec Ed]]. now subst c d g.
    + destruct (tagged_pair_decode_unique M 0 2 a b c d f ltac:(lia) ltac:(lia) Hf Hg)
        as [E _]. discriminate E.
Qed.

Theorem named_binder_absent_implication M a b f y :
  implication_graph M a b f ->
  named_binder_absent M a y -> named_binder_absent M b y -> named_binder_absent M f y.
Proof. intro H. apply named_binder_absent_implication_tagged. now apply implication_graph_tagged. Qed.

Theorem named_binder_absent_universal_tagged M a b f y :
  tagged_pair_graph M 2 a b f -> a<>y ->
  named_binder_absent M b y -> named_binder_absent M f y.
Proof.
  intros Hf Hay Hb. apply named_binder_absent_intro.
  - intros d Hd. destruct (tagged_pair_decode_unique M 2 2 a b y d f ltac:(lia) ltac:(lia) Hf Hd)
      as [_ [E _]]. exact (Hay E).
  - intros g [c [d [[Hnz [Hg Eg]] | [Hg Eg]]]].
    + destruct (tagged_pair_decode_unique M 2 0 a b c d f ltac:(lia) ltac:(lia) Hf Hg)
        as [E _]. discriminate E.
    + destruct (tagged_pair_decode_unique M 2 2 a b c d f ltac:(lia) ltac:(lia) Hf Hg)
        as [_ [Ec Ed]]. now subst c d g.
Qed.

Theorem named_binder_absent_universal M a b f y :
  universal_graph M a b f -> a<>y ->
  named_binder_absent M b y -> named_binder_absent M f y.
Proof. intro H. apply named_binder_absent_universal_tagged. now apply universal_graph_tagged. Qed.

Print Assumptions named_binder_absent_intro.
Print Assumptions named_binder_absent_zero.
Print Assumptions named_binder_absent_membership.
Print Assumptions named_binder_absent_equality.
Print Assumptions named_binder_absent_implication.
Print Assumptions named_binder_absent_universal.
