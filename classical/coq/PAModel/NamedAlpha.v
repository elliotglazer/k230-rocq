(** Proof-producing alphabetic variance.  Reverse transport uses Leibniz
    and equality symmetry, not an assumed syntactic substitution round trip. *)
From PAModel Require Import Model FiniteCoding CodeExpressions CodeDescent
  NumericalProofs ProofTemplates ProofMacros QuantifierMacros NumericalEquality
  NumericalVacuitySteps NumericalVacuity FreshNames NamedSubstitution
  NamedBinderFresh NamedLeibnizSteps NamedLeibniz NamedSubstitutionVacuity
  NamedSpecialization.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Lemma ns_proof_syl M env a b c :
  ns_proof M env (E_wim a b) -> ns_proof M env (E_wim b c) ->
  ns_proof M env (E_wim a c).
Proof.
  intros Hab Hbc.
  apply (ns_proof_macro M env (E_wim a b :: E_wim b c :: nil)).
  - intros p [<-|[<-|[]]];assumption.
  - eapply macro_syl;apply PM_input;cbn;auto.
Qed.

Lemma ns_proof_all_monotone M env x a b :
  ns_proof M env (E_wim a b) ->
  ns_proof M env (E_wim (E_wal x a) (E_wal x b)).
Proof.
  intro H. apply (ns_proof_macro M env (E_wim a b :: nil)).
  - intros p [<-|[]];exact H.
  - apply macro_all_monotone,PM_input;cbn;auto.
Qed.

Lemma ns_proof_vacuous_universal M env x y a :
  ns_proof M env (E_vac y a) -> ns_proof M env (E_vac y (E_wal x a)).
Proof.
  intro H. apply (ns_proof_macro M env (E_vac y a :: nil)).
  - intros p [<-|[]];exact H.
  - apply macro_vacuous_universal,PM_input;cbn;auto.
Qed.

Lemma ns_proof_specialize M env x y a v :
  ns_proof M env (E_wim (E_weq x y) (E_wim a v)) ->
  ns_proof M env (E_vac x v) -> ns_proof M env (E_wim (E_wal x a) v).
Proof.
  intros HL HV.
  apply (ns_proof_macro M env (E_wim (E_weq x y) (E_wim a v) :: E_vac x v :: nil)).
  - intros p [<-|[<-|[]]];assumption.
  - apply ns_macro_specialization.
Qed.

Lemma ns_proof_alpha M env x y a v :
  ns_proof M env (E_wim (E_weq x y) (E_wim a v)) ->
  ns_proof M env (E_wim (E_weq x y) (E_wim v a)) ->
  ns_proof M env (E_vac x v) -> ns_proof M env (E_vac y a) ->
  ns_proof M env (E_wim (E_wal x a) (E_wal y v)) /\
  ns_proof M env (E_wim (E_wal y v) (E_wal x a)).
Proof.
  intros HL HR VX VY. split.
  - eapply ns_proof_syl with (b:=E_wal y (E_wal x a)).
    + apply ns_proof_vacuous_universal;exact VY.
    + apply ns_proof_all_monotone.
      exact (ns_proof_specialize M env x y a v HL VX).
  - assert (HS : ns_proof M env (E_wim (E_weq y x) (E_wim v a))).
    { eapply ns_proof_syl;[apply ns_proof_symmetry|exact HR]. }
    eapply ns_proof_syl with (b:=E_wal x (E_wal y v)).
    + apply ns_proof_vacuous_universal;exact VX.
    + apply ns_proof_all_monotone.
      exact (ns_proof_specialize M env y x v a HS VY).
Qed.

Theorem numerical_named_alpha M f x y v allf allv forward backward :
  x<>y -> named_binder_absent M f x -> formula_fresh M f y ->
  named_substitution M f x y v ->
  universal_graph M x f allf -> universal_graph M y v allv ->
  implication_graph M allf allv forward -> implication_graph M allv allf backward ->
  numerically_provable M forward /\ numerically_provable M backward.
Proof.
  intros Hxy Hx Hfresh Hv Hallf Hallv Hforward Hbackward.
  pose proof (named_formula_fresh_binder_absent M f y Hfresh) as Hy.
  set (env:=code_parameters x y f v).
  destruct (code_relation_total M (E_weq (CEvar 0) (CEvar 1)) env) as [h Eh].
  assert (Hh : equality_graph M x y h).
  { exact (proj1 (expression_equality_graph M env (CEvar 0) (CEvar 1) x y h eq_refl eq_refl) Eh). }
  destruct (named_leibniz_internal M f x y h v Hh Hx Hy Hv) as [HL HR].
  assert (PL : ns_proof M env (E_wim (E_weq (CEvar 0) (CEvar 1)) (E_wim (CEvar 2) (CEvar 3)))).
  { exact (proj2 (ns_under_expression M env (E_weq (CEvar 0) (CEvar 1))
      (CEvar 2) (CEvar 3) h f v Eh eq_refl eq_refl) HL). }
  assert (PR : ns_proof M env (E_wim (E_weq (CEvar 0) (CEvar 1)) (E_wim (CEvar 3) (CEvar 2)))).
  { exact (proj2 (ns_under_expression M env (E_weq (CEvar 0) (CEvar 1))
      (CEvar 3) (CEvar 2) h v f Eh eq_refl eq_refl) HR). }
  assert (VX : ns_proof M env (E_vac (CEvar 0) (CEvar 3))).
  { intros q Hq. apply (numerical_named_substitution_vacuity M f x y v q Hxy Hx Hv).
    exact (proj1 (expression_vacuity_graph M env (CEvar 0) (CEvar 3) x v q eq_refl eq_refl) Hq). }
  assert (VY : ns_proof M env (E_vac (CEvar 1) (CEvar 2))).
  { intros q Hq. apply (numerical_vacuity M y f q Hfresh).
    exact (proj1 (expression_vacuity_graph M env (CEvar 1) (CEvar 2) y f q eq_refl eq_refl) Hq). }
  destruct (ns_proof_alpha M env (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) PL PR VX VY)
    as [PF PB].
  assert (EF : code_relation M env (E_wal (CEvar 0) (CEvar 2)) allf).
  { exact (proj2 (expression_universal_iff M env (CEvar 0) (CEvar 2) x f allf eq_refl eq_refl) Hallf). }
  assert (EV : code_relation M env (E_wal (CEvar 1) (CEvar 3)) allv).
  { exact (proj2 (expression_universal_iff M env (CEvar 1) (CEvar 3) y v allv eq_refl eq_refl) Hallv). }
  split.
  - apply PF. exact (proj2 (expression_implication_iff M env
      (E_wal (CEvar 0) (CEvar 2)) (E_wal (CEvar 1) (CEvar 3)) allf allv forward EF EV) Hforward).
  - apply PB. exact (proj2 (expression_implication_iff M env
      (E_wal (CEvar 1) (CEvar 3)) (E_wal (CEvar 0) (CEvar 2)) allv allf backward EV EF) Hbackward).
Qed.

Theorem numerical_named_alpha_total M f x y allf :
  x<>y -> named_binder_absent M f x -> formula_fresh M f y ->
  universal_graph M x f allf ->
  exists v allv forward backward,
    named_substitution M f x y v /\ universal_graph M y v allv /\
    implication_graph M allf allv forward /\ implication_graph M allv allf backward /\
    numerically_provable M forward /\ numerically_provable M backward.
Proof.
  intros Hxy Hx Hy Hall.
  destruct (named_substitution_binder_absent_total M f x y
    (named_formula_fresh_binder_absent M f y Hy)) as [v Hv].
  destruct (code_relation_total M (E_wal (CEvar 0) (CEvar 1))
    (arguments2 y v (zeroM M))) as [allv Hallv].
  destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 1))
    (arguments2 allf allv (zeroM M))) as [forward HF].
  destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 1))
    (arguments2 allv allf (zeroM M))) as [backward HB].
  exists v,allv,forward,backward. split;[exact Hv|]. split;[exact Hallv|].
  split;[exact HF|]. split;[exact HB|].
  exact (numerical_named_alpha M f x y v allf allv forward backward Hxy Hx Hy Hv Hall Hallv HF HB).
Qed.
