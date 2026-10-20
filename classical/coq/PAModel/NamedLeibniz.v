(** Internal Leibniz transport for four-tag named formula codes.
    Both variable names are absent from binder positions.  Free occurrences
    are permitted and are replaced by the checked named-substitution graph. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
  CodeDescent CodeTags NumericalProofs FreshNames FreshPropagation
  NamedSubstitutionRules NamedSubstitution NamedSubstitutionFunctionality
  NamedBinderFresh NamedLeibnizSteps.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Definition named_leibniz_property M f := forall x y h v,
  equality_graph M x y h ->
  named_binder_absent M f x -> named_binder_absent M f y ->
  named_substitution M f x y v ->
  ns_under M h f v /\ ns_under M h v f.

Definition named_leibniz_property_formula : form :=
  ∀∀∀∀ (tagged_pair_formula 3 $3 $2 $1 →
    named_binder_absent_formula $4 $3 → named_binder_absent_formula $4 $2 →
    named_substitution_formula $4 $3 $2 $0 →
    (ns_under_formula $1 $4 $0 ∧ ns_under_formula $1 $0 $4)).

Local Opaque holds tagged_pair_formula named_binder_absent_formula
  named_substitution_formula ns_under_formula.
Lemma named_leibniz_definable M : Definable1 M (named_leibniz_property M).
Proof.
  exists named_leibniz_property_formula,(fun _ => zeroM M).
  intro f. unfold named_leibniz_property_formula,named_leibniz_property.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite holds_and. setoid_rewrite tagged_pair_formula_correct.
  setoid_rewrite named_binder_absent_formula_correct.
  setoid_rewrite named_substitution_formula_correct.
  setoid_rewrite ns_under_formula_correct. reflexivity.
Qed.

Theorem named_leibniz_internal M f : named_leibniz_property M f.
Proof.
  revert f. apply (formula_code_induction M (named_leibniz_property M)).
  - apply named_leibniz_definable.
  - intros x y h v Hh Hx Hy Hv.
    rewrite (named_substitution_zero_inv M x y v Hv). split;apply ns_under_refl.
  - intros a b f Hf x y h v Hh Hx Hy Hv.
    destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
      (fun ax H rho => axioms M ax rho H) x y) as [->|Hxy].
    + rewrite (named_substitution_identity_inv M f y v Hv). split;apply ns_under_refl.
    + destruct (named_substitution_atom_inv M false a b f x y v Hxy Hf Hv)
        as [a' [b' [Ha [Hb Hout]]]].
      exact (ns_under_atom M false x y h a a' b b' f v Hh Ha Hb Hf Hout).
  - intros a b f Hf x y h v Hh Hx Hy Hv.
    destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
      (fun ax H rho => axioms M ax rho H) x y) as [->|Hxy].
    + rewrite (named_substitution_identity_inv M f y v Hv). split;apply ns_under_refl.
    + destruct (named_substitution_atom_inv M true a b f x y v Hxy Hf Hv)
        as [a' [b' [Ha [Hb Hout]]]].
      exact (ns_under_atom M true x y h a a' b b' f v Hh Ha Hb Hf Hout).
  - intros a b f Hnz Hf IHa IHb x y h v Hh Hx Hy Hv.
    destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
      (fun ax H rho => axioms M ax rho H) x y) as [->|Hxy].
    + rewrite (named_substitution_identity_inv M f y v Hv). split;apply ns_under_refl.
    + destruct (named_substitution_binary_inv M a b f x y v Hxy Hnz Hf Hv)
        as [a' [b' [Ha [Hb Hout]]]].
      assert (Ea : formula_edge M f a) by (exists a,b;left;auto).
      assert (Eb : formula_edge M f b) by (exists a,b;left;auto).
      destruct (IHa x y h a' Hh
        (named_binder_absent_child M f a x Ea Hx)
        (named_binder_absent_child M f a y Ea Hy) Ha) as [PA PA'].
      destruct (IHb x y h b' Hh
        (named_binder_absent_child M f b x Eb Hx)
        (named_binder_absent_child M f b y Eb Hy) Hb) as [PB PB'].
      apply implication_graph_tagged in Hf. apply implication_graph_tagged in Hout.
      split.
      * exact (ns_under_binary M h a a' b b' f v PA' PB Hf Hout).
      * exact (ns_under_binary M h a' a b' b v f PA PB' Hout Hf).
  - intros z a f Hf IHa x y h v Hh Hx Hy Hv.
    destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
      (fun ax H rho => axioms M ax rho H) x y) as [->|Hxy].
    + rewrite (named_substitution_identity_inv M f y v Hv). split;apply ns_under_refl.
    + pose proof (named_binder_absent_root M z a f x Hf Hx) as Hzx.
      pose proof (named_binder_absent_root M z a f y Hf Hy) as Hzy.
      destruct (named_substitution_unary_inv M z a f x y v Hxy Hzx Hf Hv)
        as [_ [a' [Ha Hout]]].
      assert (Ea : formula_edge M f a) by (exists z,a;right;auto).
      destruct (IHa x y h a' Hh
        (named_binder_absent_child M f a x Ea Hx)
        (named_binder_absent_child M f a y Ea Hy) Ha) as [PA PA'].
      apply universal_graph_tagged in Hf. apply universal_graph_tagged in Hout.
      split.
      * exact (ns_under_all M x y h z a a' f v Hh Hzx Hzy PA Hf Hout).
      * exact (ns_under_all M x y h z a' a v f Hh Hzx Hzy PA' Hout Hf).
Qed.

Corollary numerical_named_leibniz M f x y v h p q :
  named_binder_absent M f x -> named_binder_absent M f y ->
  named_substitution M f x y v -> equality_graph M x y h ->
  implication_graph M f v p -> implication_graph M h p q ->
  numerically_provable M q.
Proof.
  intros Hx Hy Hv Hh Hp Hq.
  exact (proj1 (named_leibniz_internal M f x y h v Hh Hx Hy Hv) p q Hp Hq).
Qed.

Corollary numerical_named_leibniz_reverse M f x y v h p q :
  named_binder_absent M f x -> named_binder_absent M f y ->
  named_substitution M f x y v -> equality_graph M x y h ->
  implication_graph M v f p -> implication_graph M h p q ->
  numerically_provable M q.
Proof.
  intros Hx Hy Hv Hh Hp Hq.
  exact (proj2 (named_leibniz_internal M f x y h v Hh Hx Hy Hv) p q Hp Hq).
Qed.

Theorem named_leibniz_total M f x y :
  named_binder_absent M f x -> named_binder_absent M f y ->
  exists v,named_substitution M f x y v /\ forall h,equality_graph M x y h ->
    ns_under M h f v /\ ns_under M h v f.
Proof.
  intros Hx Hy. destruct (named_substitution_binder_absent_total M f x y Hy) as [v Hv].
  exists v. split;[exact Hv|]. intros h Hh.
  exact (named_leibniz_internal M f x y h v Hh Hx Hy Hv).
Qed.
