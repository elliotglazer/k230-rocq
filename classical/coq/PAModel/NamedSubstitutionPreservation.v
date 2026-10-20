(** Internal substitution facts used to separate the free seed of KP0 from
    its bound matrix-input name. These are syntax theorems, not axioms. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
  CodeDescent CodeTags NumericalProofs FreshNames NamedBinderFresh
  NamedBinderConstructors NamedSubstitution NamedSubstitutionRules
  NamedSubstitutionFunctionality NamedSubstitutionVacuity TemplateNamedSubstitution.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition substitution_preserves_binders_property M f :=
  forall x y v z,named_substitution M f x y v ->
    named_binder_absent M f z -> named_binder_absent M v z.
Definition substitution_preserves_binders_formula : form :=
  ∀∀∀∀ (named_substitution_formula $4 $3 $2 $1 →
    named_binder_absent_formula $4 $0 → named_binder_absent_formula $1 $0).
Local Opaque holds named_substitution_formula named_binder_absent_formula.
Lemma substitution_preserves_binders_definable M :
  Definable1 M (substitution_preserves_binders_property M).
Proof.
  exists substitution_preserves_binders_formula,(fun _=>zeroM M).
  intro f. unfold substitution_preserves_binders_formula,substitution_preserves_binders_property.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite named_substitution_formula_correct.
  setoid_rewrite named_binder_absent_formula_correct. reflexivity.
Qed.

Theorem named_substitution_preserves_binders M f : substitution_preserves_binders_property M f.
Proof.
  revert f. apply (formula_code_induction M (substitution_preserves_binders_property M)).
  - apply substitution_preserves_binders_definable.
  - intros x y v z HV HZ. rewrite (named_substitution_zero_inv M x y v HV).
    apply named_binder_absent_zero.
  - intros a b f HF x y v z HV HZ.
    destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) x y) as [->|Hxy].
    + rewrite (named_substitution_identity_inv M f y v HV). exact HZ.
    + destruct (named_substitution_atom_inv M false a b f x y v Hxy HF HV)
        as [a' [b' [_ [_ HG]]]].
      exact (named_binder_absent_atom M 1 a' b' v z (or_introl eq_refl) HG).
  - intros a b f HF x y v z HV HZ.
    destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) x y) as [->|Hxy].
    + rewrite (named_substitution_identity_inv M f y v HV). exact HZ.
    + destruct (named_substitution_atom_inv M true a b f x y v Hxy HF HV)
        as [a' [b' [_ [_ HG]]]].
      exact (named_binder_absent_atom M 3 a' b' v z (or_intror eq_refl) HG).
  - intros a b f HNZ HF IHa IHb x y v z HV HZ.
    destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) x y) as [->|Hxy].
    + rewrite (named_substitution_identity_inv M f y v HV). exact HZ.
    + destruct (named_substitution_binary_inv M a b f x y v Hxy HNZ HF HV)
        as [a' [b' [HA [HB HG]]]].
      apply (named_binder_absent_implication M a' b' v z).
      * now apply implication_graph_tagged.
      * apply (IHa x y a' z HA), (named_binder_absent_child M f a z);[|exact HZ].
        exists a,b;left;auto.
      * apply (IHb x y b' z HB), (named_binder_absent_child M f b z);[|exact HZ].
        exists a,b;left;auto.
  - intros a b f HF IH x y v z HV HZ.
    destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) x y) as [->|Hxy].
    + rewrite (named_substitution_identity_inv M f y v HV). exact HZ.
    + destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
        (fun ax H rho=>axioms M ax rho H) a x) as [->|Hax].
      * rewrite (named_substitution_binder_stop_inv M x b f y v HF HV). exact HZ.
      * destruct (named_substitution_unary_inv M a b f x y v Hxy Hax HF HV)
          as [_ [b' [HB HG]]].
        apply (named_binder_absent_universal M a b' v z).
        -- now apply universal_graph_tagged.
        -- exact (named_binder_absent_root M a b f z HF HZ).
        -- apply (IH x y b' z HB), (named_binder_absent_child M f b z);[|exact HZ].
           exists a,b;right;auto.
Qed.

Definition substitution_erases_source_property M f := forall x y z v,
  x<>y -> named_binder_absent M f x -> named_binder_absent M f z ->
  named_substitution M f x y v -> named_substitution M v x z v.
Definition substitution_erases_source_formula : form :=
  ∀∀∀∀ (¬($3==$2) → named_binder_absent_formula $4 $3 →
    named_binder_absent_formula $4 $1 → named_substitution_formula $4 $3 $2 $0 →
    named_substitution_formula $0 $3 $1 $0).
Lemma substitution_erases_source_definable M :
  Definable1 M (substitution_erases_source_property M).
Proof.
  exists substitution_erases_source_formula,(fun _=>zeroM M).
  intro f. unfold substitution_erases_source_formula,substitution_erases_source_property.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite named_substitution_formula_correct.
  setoid_rewrite named_binder_absent_formula_correct. reflexivity.
Qed.

Theorem named_substitution_erases_source M f : substitution_erases_source_property M f.
Proof.
  revert f. apply (formula_code_induction M (substitution_erases_source_property M)).
  - apply substitution_erases_source_definable.
  - intros x y z v Hxy HX HZ HV. rewrite (named_substitution_zero_inv M x y v HV).
    apply named_substitution_zero.
  - intros a b f HF x y z v Hxy HX HZ HV.
    destruct (named_substitution_atom_inv M false a b f x y v Hxy HF HV)
      as [a' [b' [HA [HB HG]]]].
    apply (ns_combine_atom M false a' b' v a' b' v x z HG HG).
    + right;split;[|reflexivity]. intro E.
      exact (named_replace_avoids_source M x y a a' Hxy HA (Logic.eq_sym E)).
    + right;split;[|reflexivity]. intro E.
      exact (named_replace_avoids_source M x y b b' Hxy HB (Logic.eq_sym E)).
  - intros a b f HF x y z v Hxy HX HZ HV.
    destruct (named_substitution_atom_inv M true a b f x y v Hxy HF HV)
      as [a' [b' [HA [HB HG]]]].
    apply (ns_combine_atom M true a' b' v a' b' v x z HG HG).
    + right;split;[|reflexivity]. intro E.
      exact (named_replace_avoids_source M x y a a' Hxy HA (Logic.eq_sym E)).
    + right;split;[|reflexivity]. intro E.
      exact (named_replace_avoids_source M x y b b' Hxy HB (Logic.eq_sym E)).
  - intros a b f HNZ HF IHa IHb x y z v Hxy HX HZ HV.
    destruct (named_substitution_binary_inv M a b f x y v Hxy HNZ HF HV)
      as [a' [b' [HA [HB HG]]]].
    apply implication_graph_tagged in HG.
    apply (ns_combine_implication M a' b' v a' b' v x z HG HG).
    + apply (IHa x y z a' Hxy);[| |exact HA];
        apply (named_binder_absent_child M f a);try assumption;exists a,b;left;auto.
    + apply (IHb x y z b' Hxy);[| |exact HB];
        apply (named_binder_absent_child M f b);try assumption;exists a,b;left;auto.
  - intros a b f HF IH x y z v Hxy HX HZ HV.
    pose proof (named_binder_absent_root M a b f x HF HX) as Hax.
    pose proof (named_binder_absent_root M a b f z HF HZ) as Haz.
    destruct (named_substitution_unary_inv M a b f x y v Hxy Hax HF HV)
      as [_ [b' [HB HG]]].
    apply universal_graph_tagged in HG.
    apply (ns_combine_universal M a b' v b' v x z Hax Haz HG HG).
    apply (IH x y z b' Hxy);[| |exact HB];
      apply (named_binder_absent_child M f b);try assumption;exists a,b;right;auto.
Qed.

Print Assumptions named_substitution_preserves_binders.
Print Assumptions named_substitution_erases_source.
