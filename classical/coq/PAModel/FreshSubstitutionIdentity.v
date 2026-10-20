(** Substitution leaves a source-fresh internal formula unchanged. The
    replacement still avoids binders because the checked substitution
    relation rejects capture even in an unused branch. *)
From PAModel Require Import Model FiniteCoding CodeExpressions CodeDescent
  CodeTags NumericalProofs FreshNames FreshPropagation NamedBinderFresh
  NamedSubstitution NamedSubstitutionRules TemplateNamedSubstitution.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition fresh_substitution_identity_property M f := forall x y,
  formula_fresh M f x -> named_binder_absent M f y -> named_substitution M f x y f.
Definition fresh_substitution_identity_formula : form :=
  ∀∀ (formula_fresh_formula $2 $1 → named_binder_absent_formula $2 $0 →
    named_substitution_formula $2 $1 $0 $2).

Local Opaque holds formula_fresh_formula named_binder_absent_formula named_substitution_formula.

Lemma fresh_substitution_identity_definable M :
  Definable1 M (fresh_substitution_identity_property M).
Proof.
  exists fresh_substitution_identity_formula,(fun _=>zeroM M).
  intro f. unfold fresh_substitution_identity_formula,fresh_substitution_identity_property.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite formula_fresh_formula_correct.
  setoid_rewrite named_binder_absent_formula_correct.
  setoid_rewrite named_substitution_formula_correct. reflexivity.
Qed.

Theorem named_substitution_source_fresh M f x y :
  formula_fresh M f x -> named_binder_absent M f y -> named_substitution M f x y f.
Proof.
  revert x y. change (fresh_substitution_identity_property M f). revert f.
  apply (formula_code_induction M (fresh_substitution_identity_property M)).
    - apply fresh_substitution_identity_definable.
    - intros a b Hfresh Hbind. apply named_substitution_zero.
    - intros a b f Hf x' y' Hfresh Hbind.
      destruct (formula_fresh_membership M a b f x' Hf Hfresh) as [HA HB].
      apply (ns_combine_atom M false a b f a b f x' y');try exact Hf;now right.
    - intros a b f Hf x' y' Hfresh Hbind.
      destruct (formula_fresh_equality M a b f x' Hf Hfresh) as [HA HB].
      apply (ns_combine_atom M true a b f a b f x' y');try exact Hf;now right.
    - intros a b f Hnz Hf IHa IHb x' y' Hfresh Hbind.
      assert (EA:formula_edge M f a) by (exists a,b;left;auto).
      assert (EB:formula_edge M f b) by (exists a,b;left;auto).
      apply (ns_combine_implication M a b f a b f x' y').
      + now apply implication_graph_tagged.
      + now apply implication_graph_tagged.
      + apply IHa.
        * exact (formula_fresh_child M f a x' Hfresh EA).
        * exact (named_binder_absent_child M f a y' EA Hbind).
      + apply IHb.
        * exact (formula_fresh_child M f b x' Hfresh EB).
        * exact (named_binder_absent_child M f b y' EB Hbind).
    - intros z a f Hf IH x' y' Hfresh Hbind.
      destruct (formula_fresh_universal_tagged M z a f x' Hf Hfresh) as [HZX HA].
      assert (HZY:z<>y') by exact (named_binder_absent_root M z a f y' Hf Hbind).
      assert (EA:formula_edge M f a) by (exists z,a;right;auto).
      apply (ns_combine_universal M z a f a f x' y' HZX HZY).
      + now apply universal_graph_tagged.
      + now apply universal_graph_tagged.
      + apply IH;[exact HA|]. exact (named_binder_absent_child M f a y' EA Hbind).
Qed.

Print Assumptions named_substitution_source_fresh.
