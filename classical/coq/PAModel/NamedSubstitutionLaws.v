(** Exact constructor equations for the conservative named substitution.
    No theorem here supplies a numerical K proof of instantiation. *)
From PAModel Require Import Model FiniteCoding NumericalProofs CodeDescent CodeTags FreshNames
  NamedSubstitutionRules NamedSubstitution NamedSubstitutionFunctionality.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Theorem named_substitution_stop_iff M f x y v :
  named_sub_stop M f x y -> (named_substitution M f x y v <-> v=f).
Proof.
  intro Hstop. split.
  - intro H. destruct Hstop as [->|[->|[b Hb]]].
    + now apply named_substitution_identity_inv in H.
    + now apply named_substitution_zero_inv in H.
    + exact (named_substitution_binder_stop_inv M x b f y v Hb H).
  - intro E. subst v. now apply named_substitution_stop.
Qed.

Theorem named_substitution_atom_iff M eq a b f x y v :
  x<>y -> tagged_pair_graph M (named_atom_tag eq) a b f ->
  (named_substitution M f x y v <->
   exists a' b',named_replace M x y a a' /\ named_replace M x y b b' /\
     tagged_pair_graph M (named_atom_tag eq) a' b' v).
Proof.
  intros Hxy Hf. split.
  - apply named_substitution_atom_inv;assumption.
  - intros [a' [b' [Ha [Hb Hv]]]].
    exact (named_substitution_atom_intro M eq a b f x y a' b' v Hxy Hf Ha Hb Hv).
Qed.

Theorem named_substitution_implication_iff M a b f x y v :
  x<>y -> f<>zeroM M -> implication_graph M a b f ->
  (named_substitution M f x y v <->
   exists a' b',named_substitution M a x y a' /\ named_substitution M b x y b' /\
     implication_graph M a' b' v).
Proof.
  intros Hxy Hnz Hf. apply implication_graph_tagged in Hf. split.
  - intro H. destruct (named_substitution_binary_inv M a b f x y v Hxy Hnz Hf H)
      as [a' [b' [Ha [Hb Hv]]]]. exists a',b'. split;[exact Ha|]. split;[exact Hb|].
    now apply implication_graph_tagged.
  - intros [a' [b' [Ha [Hb Hv]]]]. apply implication_graph_tagged in Hv.
    exact (named_substitution_binary_intro M a b f x y a' b' v Hxy Hnz Hf Ha Hb Hv).
Qed.

Theorem named_substitution_universal_iff M a b f x y v :
  x<>y -> a<>x -> universal_graph M a b f ->
  (named_substitution M f x y v <->
   a<>y /\ exists w,named_substitution M b x y w /\ universal_graph M a w v).
Proof.
  intros Hxy Hax Hf. apply universal_graph_tagged in Hf. split.
  - intro H. destruct (named_substitution_unary_inv M a b f x y v Hxy Hax Hf H)
      as [Hay [w [Hw Hv]]]. split;[exact Hay|]. exists w. split;[exact Hw|].
    now apply universal_graph_tagged.
  - intros [Hay [w [Hw Hv]]]. apply universal_graph_tagged in Hv.
    exact (named_substitution_unary_intro M a b f x y w v Hxy Hax Hay Hf Hw Hv).
Qed.

Theorem named_substitution_rejects_capture M x y b f v :
  x<>y -> universal_graph M y b f -> ~named_substitution M f x y v.
Proof.
  intros Hxy Hf H. apply (proj1 (named_substitution_universal_iff M y b f x y v
    Hxy (fun E=>Hxy (eq_sym E)) Hf)) in H. exact (proj1 H eq_refl).
Qed.

Theorem named_substitution_to_fresh_name M f x :
  exists v,named_substitution M f x (succM M f) v.
Proof. apply named_substitution_fresh_total,formula_successor_is_fresh. Qed.
