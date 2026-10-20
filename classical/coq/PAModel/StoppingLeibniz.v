(** Leibniz transport for the existing capture-rejecting substitution. Inner
    binders equal to the source name stop substitution and use reflexivity.
    Only the replacement name is excluded from binder positions. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
  CodeDescent CodeTags NumericalProofs FreshNames FreshPropagation
  NamedSubstitutionRules NamedSubstitution NamedSubstitutionFunctionality
  NamedBinderFresh NamedLeibnizSteps.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Definition stopping_leibniz_property M f := forall x y h v,
  equality_graph M x y h ->
  named_binder_absent M f y ->
  named_substitution M f x y v ->
  ns_under M h f v /\ ns_under M h v f.

Definition stopping_leibniz_property_formula : form :=
  ∀∀∀∀ (tagged_pair_formula 3 $3 $2 $1 →
    named_binder_absent_formula $4 $2 →
    named_substitution_formula $4 $3 $2 $0 →
    (ns_under_formula $1 $4 $0 ∧ ns_under_formula $1 $0 $4)).

Local Opaque holds tagged_pair_formula named_binder_absent_formula
  named_substitution_formula ns_under_formula.
Lemma stopping_leibniz_definable M : Definable1 M (stopping_leibniz_property M).
Proof.
  exists stopping_leibniz_property_formula,(fun _ => zeroM M).
  intro f. unfold stopping_leibniz_property_formula,stopping_leibniz_property.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite holds_and. setoid_rewrite tagged_pair_formula_correct.
  setoid_rewrite named_binder_absent_formula_correct.
  setoid_rewrite named_substitution_formula_correct.
  setoid_rewrite ns_under_formula_correct. reflexivity.
Qed.

Theorem stopping_leibniz_internal M f : stopping_leibniz_property M f.
Proof.
  revert f. apply (formula_code_induction M (stopping_leibniz_property M)).
  - apply stopping_leibniz_definable.
  - intros x y h v Hh Hy Hv.
    rewrite (named_substitution_zero_inv M x y v Hv). split;apply ns_under_refl.
  - intros a b f Hf x y h v Hh Hy Hv.
    destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
      (fun ax H rho => axioms M ax rho H) x y) as [->|Hxy].
    + rewrite (named_substitution_identity_inv M f y v Hv). split;apply ns_under_refl.
    + destruct (named_substitution_atom_inv M false a b f x y v Hxy Hf Hv)
        as [a' [b' [Ha [Hb Hout]]]].
      exact (ns_under_atom M false x y h a a' b b' f v Hh Ha Hb Hf Hout).
  - intros a b f Hf x y h v Hh Hy Hv.
    destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
      (fun ax H rho => axioms M ax rho H) x y) as [->|Hxy].
    + rewrite (named_substitution_identity_inv M f y v Hv). split;apply ns_under_refl.
    + destruct (named_substitution_atom_inv M true a b f x y v Hxy Hf Hv)
        as [a' [b' [Ha [Hb Hout]]]].
      exact (ns_under_atom M true x y h a a' b b' f v Hh Ha Hb Hf Hout).
  - intros a b f Hnz Hf IHa IHb x y h v Hh Hy Hv.
    destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
      (fun ax H rho => axioms M ax rho H) x y) as [->|Hxy].
    + rewrite (named_substitution_identity_inv M f y v Hv). split;apply ns_under_refl.
    + destruct (named_substitution_binary_inv M a b f x y v Hxy Hnz Hf Hv)
        as [a' [b' [Ha [Hb Hout]]]].
      assert (Ea : formula_edge M f a) by (exists a,b;left;auto).
      assert (Eb : formula_edge M f b) by (exists a,b;left;auto).
      destruct (IHa x y h a' Hh
        (named_binder_absent_child M f a y Ea Hy) Ha) as [PA PA'].
      destruct (IHb x y h b' Hh
        (named_binder_absent_child M f b y Eb Hy) Hb) as [PB PB'].
      apply implication_graph_tagged in Hf. apply implication_graph_tagged in Hout.
      split.
      * exact (ns_under_binary M h a a' b b' f v PA' PB Hf Hout).
      * exact (ns_under_binary M h a' a b' b v f PA PB' Hout Hf).
  - intros z a f Hf IHa x y h v Hh Hy Hv.
    destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
      (fun ax H rho => axioms M ax rho H) x y) as [->|Hxy].
    + rewrite (named_substitution_identity_inv M f y v Hv). split;apply ns_under_refl.
    + destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
        (fun ax H rho => axioms M ax rho H) z x) as [->|Hzx].
      * assert (E : v=f).
        { eapply named_substitution_functional;[exact Hv|].
          apply (named_substitution_binder_stop M x a f y). exact Hf. }
        subst v. split;apply ns_under_refl.
      * pose proof (named_binder_absent_root M z a f y Hf Hy) as Hzy.
      destruct (named_substitution_unary_inv M z a f x y v Hxy Hzx Hf Hv)
        as [_ [a' [Ha Hout]]].
      assert (Ea : formula_edge M f a) by (exists z,a;right;auto).
      destruct (IHa x y h a' Hh
        (named_binder_absent_child M f a y Ea Hy) Ha) as [PA PA'].
      apply universal_graph_tagged in Hf. apply universal_graph_tagged in Hout.
      split.
      -- exact (ns_under_all M x y h z a a' f v Hh Hzx Hzy PA Hf Hout).
      -- exact (ns_under_all M x y h z a' a v f Hh Hzx Hzy PA' Hout Hf).
Qed.


Print Assumptions stopping_leibniz_internal.
