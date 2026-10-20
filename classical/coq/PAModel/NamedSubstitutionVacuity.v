(** Direct proof-producing vacuity for a substituted formula.  The source
    name is excluded from binder positions, and its replacement is distinct.
    No global reachability theorem about freshness of the output is assumed. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
  CodeDescent CodeTags NumericalProofs FreshNames FreshPropagation
  NamedSubstitutionRules NamedSubstitution NamedSubstitutionFunctionality
  NamedBinderFresh NamedLeibnizSteps NumericalVacuitySteps NumericalVacuity.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Lemma named_replace_avoids_source M x y a a' :
  x<>y -> named_replace M x y a a' -> x<>a'.
Proof. intros Hxy [[-> ->]|[Hax ->]];congruence. Qed.

Definition named_substitution_vacuity_property M f := forall x y v,
  x<>y -> named_binder_absent M f x -> named_substitution M f x y v ->
  forall q,vacuity_graph M x v q -> numerically_provable M q.

Definition named_substitution_vacuity_formula : form :=
  ∀∀∀ (¬($2==$1) → named_binder_absent_formula $3 $2 →
    named_substitution_formula $3 $2 $1 $0 →
    ∀ (vacuity_formula $3 $1 $0 → numerically_provable_formula $0)).

Local Opaque holds named_binder_absent_formula named_substitution_formula
  vacuity_formula numerically_provable_formula.
Lemma named_substitution_vacuity_definable M :
  Definable1 M (named_substitution_vacuity_property M).
Proof.
  exists named_substitution_vacuity_formula,(fun _ => zeroM M).
  intro f. unfold named_substitution_vacuity_formula,named_substitution_vacuity_property.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite named_binder_absent_formula_correct.
  setoid_rewrite named_substitution_formula_correct.
  setoid_rewrite vacuity_formula_correct.
  setoid_rewrite numerically_provable_formula_correct. reflexivity.
Qed.

Theorem named_substitution_vacuity_internal M f : named_substitution_vacuity_property M f.
Proof.
  revert f. apply (formula_code_induction M (named_substitution_vacuity_property M)).
  - apply named_substitution_vacuity_definable.
  - intros x y v Hxy Hx Hv q Hq.
    rewrite (named_substitution_zero_inv M x y v Hv) in Hq.
    apply (numerical_vacuity_truth M (x .: fun _ => zeroM M) (CEvar 0) q).
    exact (proj2 (expression_vacuity_graph M _ (CEvar 0) (CEconst 0)
      x (zeroM M) q eq_refl eq_refl) Hq).
  - intros a b f Hf x y v Hxy Hx Hv q Hq.
    destruct (named_substitution_atom_inv M false a b f x y v Hxy Hf Hv)
      as [a' [b' [Ha [Hb Hout]]]].
    exact (numerical_atom_vacuity M false a' b' v x q Hout
      (named_replace_avoids_source M x y a a' Hxy Ha)
      (named_replace_avoids_source M x y b b' Hxy Hb) Hq).
  - intros a b f Hf x y v Hxy Hx Hv q Hq.
    destruct (named_substitution_atom_inv M true a b f x y v Hxy Hf Hv)
      as [a' [b' [Ha [Hb Hout]]]].
    exact (numerical_atom_vacuity M true a' b' v x q Hout
      (named_replace_avoids_source M x y a a' Hxy Ha)
      (named_replace_avoids_source M x y b b' Hxy Hb) Hq).
  - intros a b f Hnz Hf IHa IHb x y v Hxy Hx Hv q Hq.
    destruct (named_substitution_binary_inv M a b f x y v Hxy Hnz Hf Hv)
      as [a' [b' [Ha [Hb Hout]]]].
    assert (Ea : formula_edge M f a) by (exists a,b;left;auto).
    assert (Eb : formula_edge M f b) by (exists a,b;left;auto).
    destruct (vacuity_graph_total M x a') as [qa Hqa].
    destruct (vacuity_graph_total M x b') as [qb Hqb].
    pose proof (IHa x y a' Hxy (named_binder_absent_child M f a x Ea Hx) Ha qa Hqa) as PA.
    pose proof (IHb x y b' Hxy (named_binder_absent_child M f b x Eb Hx) Hb qb Hqb) as PB.
    set (env:=x .: a' .: b' .: fun _ => zeroM M).
    apply implication_graph_tagged in Hout.
    assert (Ev : code_relation M env (E_wim (CEvar 1) (CEvar 2)) v).
    { exact (proj2 (expression_implication_iff M env (CEvar 1) (CEvar 2) a' b' v eq_refl eq_refl) Hout). }
    apply (numerical_vacuity_implication M env (CEvar 0) (CEvar 1) (CEvar 2) qa qb q).
    + exact (proj2 (expression_vacuity_graph M env (CEvar 0) (CEvar 1) x a' qa eq_refl eq_refl) Hqa).
    + exact (proj2 (expression_vacuity_graph M env (CEvar 0) (CEvar 2) x b' qb eq_refl eq_refl) Hqb).
    + exact (proj2 (expression_vacuity_graph M env (CEvar 0) (E_wim (CEvar 1) (CEvar 2)) x v q eq_refl Ev) Hq).
    + exact PA.
    + exact PB.
  - intros z a f Hf IHa x y v Hxy Hx Hv q Hq.
    pose proof (named_binder_absent_root M z a f x Hf Hx) as Hzx.
    destruct (named_substitution_unary_inv M z a f x y v Hxy Hzx Hf Hv)
      as [_ [a' [Ha Hout]]].
    assert (Ea : formula_edge M f a) by (exists z,a;right;auto).
    destruct (vacuity_graph_total M x a') as [qa Hqa].
    pose proof (IHa x y a' Hxy (named_binder_absent_child M f a x Ea Hx) Ha qa Hqa) as PA.
    set (env:=x .: z .: a' .: fun _ => zeroM M).
    apply universal_graph_tagged in Hout.
    assert (Ev : code_relation M env (E_wal (CEvar 1) (CEvar 2)) v).
    { exact (proj2 (expression_universal_iff M env (CEvar 1) (CEvar 2) z a' v eq_refl eq_refl) Hout). }
    apply (numerical_vacuity_universal M env (CEvar 1) (CEvar 0) (CEvar 2) qa q).
    + exact (proj2 (expression_vacuity_graph M env (CEvar 0) (CEvar 2) x a' qa eq_refl eq_refl) Hqa).
    + exact (proj2 (expression_vacuity_graph M env (CEvar 0) (E_wal (CEvar 1) (CEvar 2)) x v q eq_refl Ev) Hq).
    + exact PA.
Qed.

Corollary numerical_named_substitution_vacuity M f x y v q :
  x<>y -> named_binder_absent M f x -> named_substitution M f x y v ->
  vacuity_graph M x v q -> numerically_provable M q.
Proof. intros Hxy Hx Hv. exact (named_substitution_vacuity_internal M f x y v Hxy Hx Hv q). Qed.
