(** Bound-variable vacuity with shadowing. The helper and structural
    induction are separated: the helper uses output-vacuity of one body;
    the induction invokes that helper only on strictly smaller bodies. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  CodeDescent CodeTags BetaExtension NumericalProofs NumericalEquality
  NumericalVacuitySteps NumericalVacuity FreshNames NamedSubstitution
  NamedSubstitutionRules NamedSubstitutionFunctionality NamedBinderFresh
  NamedLeibnizSteps NamedSubstitutionVacuity NamedAlpha StoppingLeibniz.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Definition stopping_substitution_vacuity_property M f := forall x y v,
  x<>y -> named_substitution M f x y v ->
  forall q,vacuity_graph M x v q -> numerically_provable M q.

Lemma bound_vacuity_from_substitution M f :
  stopping_substitution_vacuity_property M f ->
  forall x allf result,universal_graph M x f allf ->
  vacuity_graph M x allf result -> numerically_provable M result.
Proof.
  intros PV x allf result HAll HResult.
  set (y:=succM M (addM M x f)).
  assert (HXY : coding_lt M x y) by (unfold y;apply coding_le_add).
  assert (HFY : coding_lt M f y).
  { unfold y. rewrite Arithmetic.add_comm. apply coding_le_add. }
  assert (Hxy : x<>y).
  { exact (@Peano.lt_neq (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) x y HXY). }
  pose proof (formula_above_is_fresh M f y HFY) as HYFresh.
  pose proof (named_formula_fresh_binder_absent M f y HYFresh) as HY.
  destruct (named_substitution_binder_absent_total M f x y HY) as [v HV].
  set (env:=code_parameters x y f v).
  destruct (code_relation_total M (E_weq (CEvar 0) (CEvar 1)) env) as [eq HEq].
  assert (HE : equality_graph M x y eq).
  { exact (proj1 (expression_equality_graph M env (CEvar 0) (CEvar 1) x y eq eq_refl eq_refl) HEq). }
  destruct (stopping_leibniz_internal M f x y eq v HE HY HV) as [HForward HBack].
  assert (PL : ns_proof M env (E_wim (E_weq (CEvar 0) (CEvar 1)) (E_wim (CEvar 2) (CEvar 3)))).
  { exact (proj2 (ns_under_expression M env (E_weq (CEvar 0) (CEvar 1))
      (CEvar 2) (CEvar 3) eq f v HEq eq_refl eq_refl) HForward). }
  assert (PR : ns_proof M env (E_wim (E_weq (CEvar 0) (CEvar 1)) (E_wim (CEvar 3) (CEvar 2)))).
  { exact (proj2 (ns_under_expression M env (E_weq (CEvar 0) (CEvar 1))
      (CEvar 3) (CEvar 2) eq v f HEq eq_refl eq_refl) HBack). }
  assert (VX : ns_proof M env (E_vac (CEvar 0) (CEvar 3))).
  { intros q HQ. apply (PV x y v Hxy HV q).
    exact (proj1 (expression_vacuity_graph M env (CEvar 0) (CEvar 3) x v q eq_refl eq_refl) HQ). }
  assert (VY : ns_proof M env (E_vac (CEvar 1) (CEvar 2))).
  { intros q HQ. apply (numerical_vacuity M y f q HYFresh).
    exact (proj1 (expression_vacuity_graph M env (CEvar 1) (CEvar 2) y f q eq_refl eq_refl) HQ). }
  destruct (ns_proof_alpha M env (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)
    PL PR VX VY) as [PA PB].
  assert (PVall : ns_proof M env (E_vac (CEvar 0) (E_wal (CEvar 1) (CEvar 3)))).
  { now apply ns_proof_vacuous_universal. }
  assert (HP : ns_proof M env (E_vac (CEvar 0) (E_wal (CEvar 0) (CEvar 2)))).
  { unfold E_vac.
    eapply ns_proof_syl;[exact PA|].
    eapply ns_proof_syl;[exact PVall|].
    now apply ns_proof_all_monotone. }
  assert (HA : code_relation M env (E_wal (CEvar 0) (CEvar 2)) allf).
  { exact (proj2 (expression_universal_iff M env (CEvar 0) (CEvar 2)
      x f allf eq_refl eq_refl) HAll). }
  apply HP.
  exact (proj2 (expression_vacuity_graph M env (CEvar 0)
    (E_wal (CEvar 0) (CEvar 2)) x allf result eq_refl HA) HResult).
Qed.

Definition stopping_substitution_vacuity_formula : form :=
  ∀∀∀ (¬($2==$1) →
    named_substitution_formula $3 $2 $1 $0 →
    ∀ (vacuity_formula $3 $1 $0 → numerically_provable_formula $0)).

Local Opaque holds named_binder_absent_formula named_substitution_formula
  vacuity_formula numerically_provable_formula.
Lemma stopping_substitution_vacuity_definable M :
  Definable1 M (stopping_substitution_vacuity_property M).
Proof.
  exists stopping_substitution_vacuity_formula,(fun _ => zeroM M).
  intro f. unfold stopping_substitution_vacuity_formula,stopping_substitution_vacuity_property.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite named_substitution_formula_correct.
  setoid_rewrite vacuity_formula_correct.
  setoid_rewrite numerically_provable_formula_correct. reflexivity.
Qed.

Theorem stopping_substitution_vacuity_internal M f : stopping_substitution_vacuity_property M f.
Proof.
  revert f. apply (formula_code_induction M (stopping_substitution_vacuity_property M)).
  - apply stopping_substitution_vacuity_definable.
  - intros x y v Hxy Hv q Hq.
    rewrite (named_substitution_zero_inv M x y v Hv) in Hq.
    apply (numerical_vacuity_truth M (x .: fun _ => zeroM M) (CEvar 0) q).
    exact (proj2 (expression_vacuity_graph M _ (CEvar 0) (CEconst 0)
      x (zeroM M) q eq_refl eq_refl) Hq).
  - intros a b f Hf x y v Hxy Hv q Hq.
    destruct (named_substitution_atom_inv M false a b f x y v Hxy Hf Hv)
      as [a' [b' [Ha [Hb Hout]]]].
    exact (numerical_atom_vacuity M false a' b' v x q Hout
      (named_replace_avoids_source M x y a a' Hxy Ha)
      (named_replace_avoids_source M x y b b' Hxy Hb) Hq).
  - intros a b f Hf x y v Hxy Hv q Hq.
    destruct (named_substitution_atom_inv M true a b f x y v Hxy Hf Hv)
      as [a' [b' [Ha [Hb Hout]]]].
    exact (numerical_atom_vacuity M true a' b' v x q Hout
      (named_replace_avoids_source M x y a a' Hxy Ha)
      (named_replace_avoids_source M x y b b' Hxy Hb) Hq).
  - intros a b f Hnz Hf IHa IHb x y v Hxy Hv q Hq.
    destruct (named_substitution_binary_inv M a b f x y v Hxy Hnz Hf Hv)
      as [a' [b' [Ha [Hb Hout]]]].
    assert (Ea : formula_edge M f a) by (exists a,b;left;auto).
    assert (Eb : formula_edge M f b) by (exists a,b;left;auto).
    destruct (vacuity_graph_total M x a') as [qa Hqa].
    destruct (vacuity_graph_total M x b') as [qb Hqb].
    pose proof (IHa x y a' Hxy Ha qa Hqa) as PA.
    pose proof (IHb x y b' Hxy Hb qb Hqb) as PB.
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
  - intros z a f Hf IHa x y v Hxy Hv q Hq.
    destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) z x) as [->|Hzx].
    + assert (E : v=f).
      { eapply named_substitution_functional;[exact Hv|].
        exact (named_substitution_binder_stop M x a f y Hf). }
      subst v. apply (bound_vacuity_from_substitution M a IHa x f q);[|exact Hq].
      now apply universal_graph_tagged.
    + destruct (named_substitution_unary_inv M z a f x y v Hxy Hzx Hf Hv)
      as [_ [a' [Ha Hout]]].
    assert (Ea : formula_edge M f a) by (exists z,a;right;auto).
    destruct (vacuity_graph_total M x a') as [qa Hqa].
    pose proof (IHa x y a' Hxy Ha qa Hqa) as PA.
    set (env:=x .: z .: a' .: fun _ => zeroM M).
    apply universal_graph_tagged in Hout.
    assert (Ev : code_relation M env (E_wal (CEvar 1) (CEvar 2)) v).
    { exact (proj2 (expression_universal_iff M env (CEvar 1) (CEvar 2) z a' v eq_refl eq_refl) Hout). }
    apply (numerical_vacuity_universal M env (CEvar 1) (CEvar 0) (CEvar 2) qa q).
      * exact (proj2 (expression_vacuity_graph M env (CEvar 0) (CEvar 2) x a' qa eq_refl eq_refl) Hqa).
      * exact (proj2 (expression_vacuity_graph M env (CEvar 0) (E_wal (CEvar 1) (CEvar 2)) x v q eq_refl Ev) Hq).
      * exact PA.
Qed.

Theorem numerical_bound_variable_vacuity M f x allf result :
  universal_graph M x f allf -> vacuity_graph M x allf result ->
  numerically_provable M result.
Proof. apply bound_vacuity_from_substitution,stopping_substitution_vacuity_internal. Qed.

Print Assumptions bound_vacuity_from_substitution.
Print Assumptions stopping_substitution_vacuity_internal.
Print Assumptions numerical_bound_variable_vacuity.
