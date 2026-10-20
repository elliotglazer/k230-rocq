(** Numerical request formulas and checked substitution of their input role.
    Their output and container names remain fixed. The source input name is
    explicitly nonzero because the actual falsity code is membership 0 0. *)
From PAModel Require Import Model FiniteCoding CodeExpressions CodeDescent NumericalProofs FreshNames
  ProofTemplates TemplatePropositional ProofMacros QuantifierMacros NumericalVacuitySteps
  NamedLeibnizSteps NamedLeibniz NamedBinderFresh NamedSubstitution NamedSubstitutionRules
  TemplateBinderFresh TemplateNamedSubstitution NamedExistential NamedAlpha
  NumericalKP0 BoundVariableVacuityRules NumericalEquality NumericalBootstrap
  NamedSpecialization.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Definition E_kp_request b k m :=
  E_wim (E_wex b m) (E_wex b (E_wa (E_wel b k) m)).

Definition request_parameters M (a b k p m mp : carrier M) :=
  a .: b .: k .: p .: m .: mp .: fun _=>zeroM M.

Theorem request_input_substitution M a b k p m mp r rp :
  a<>zeroM M -> b<>a -> b<>p -> k<>a ->
  named_substitution M m a p mp ->
  code_relation M (request_parameters M a b k p m mp)
    (E_kp_request (CEvar 1) (CEvar 2) (CEvar 4)) r ->
  code_relation M (request_parameters M a b k p m mp)
    (E_kp_request (CEvar 1) (CEvar 2) (CEvar 5)) rp ->
  named_substitution M r a p rp.
Proof.
  intros HA HBA HBP HKA HM HR HRP.
  set (rho:=request_parameters M a b k p m mp).
  assert (HMat : expression_named_substitution M rho rho a p (CEvar 4) (CEvar 5)).
  { intros u v HU HV. change (u=m) in HU. change (v=mp) in HV. now subst u v. }
  assert (HMem : expression_named_substitution M rho rho a p
    (E_wel (CEvar 1) (CEvar 2)) (E_wel (CEvar 1) (CEvar 2))).
  { apply (expression_ns_atom M rho rho a p false).
    - intros u v HU HV. change (u=b) in HU. change (v=b) in HV. subst u v.
      now right.
    - intros u v HU HV. change (u=k) in HU. change (v=k) in HV. subst u v.
      now right. }
  apply (expression_ns_implication M rho rho a p
    (E_wex (CEvar 1) (CEvar 4)) (E_wex (CEvar 1) (E_wa (E_wel (CEvar 1) (CEvar 2)) (CEvar 4)))
    (E_wex (CEvar 1) (CEvar 5)) (E_wex (CEvar 1) (E_wa (E_wel (CEvar 1) (CEvar 2)) (CEvar 5)))).
  - exact (expression_ns_existential M rho rho a p (CEvar 1) (CEvar 1)
      (CEvar 4) (CEvar 5) b HA eq_refl eq_refl HBA HBP HMat).
  - apply (expression_ns_existential M rho rho a p (CEvar 1) (CEvar 1)
      (E_wa (E_wel (CEvar 1) (CEvar 2)) (CEvar 4))
      (E_wa (E_wel (CEvar 1) (CEvar 2)) (CEvar 5)) b HA eq_refl eq_refl HBA HBP).
    exact (expression_ns_conjunction M rho rho a p _ _ _ _ HA HMem HMat).
  - exact HR.
  - exact HRP.
Qed.

Lemma request_binder_absent M rho B K F b name :
  code_relation M rho B b -> b<>name -> expression_binder_absent M rho name F ->
  expression_binder_absent M rho name (E_kp_request B K F).
Proof.
  intros HB HBN HF. unfold E_kp_request. apply expression_binder_absent_implication.
  - apply expression_binder_absent_existential.
    + intros v HV. rewrite (code_relation_functional M B rho v b HV HB). exact HBN.
    + exact HF.
  - apply expression_binder_absent_existential.
    + intros v HV. rewrite (code_relation_functional M B rho v b HV HB). exact HBN.
    + apply expression_binder_absent_conjunction;[|exact HF].
      apply expression_binder_absent_atom. now left.
Qed.

Theorem numerical_request_input_congruence M a b k p m mp :
  a<>zeroM M -> b<>a -> b<>p -> k<>a ->
  named_binder_absent M m a -> named_binder_absent M m p ->
  named_substitution M m a p mp ->
  ns_proof M (request_parameters M a b k p m mp)
    (E_wim (E_weq (CEvar 0) (CEvar 3))
      (E_wim (E_kp_request (CEvar 1) (CEvar 2) (CEvar 4))
        (E_kp_request (CEvar 1) (CEvar 2) (CEvar 5)))).
Proof.
  intros HA HBA HBP HKA HMA HMP HM.
  set (rho:=request_parameters M a b k p m mp).
  destruct (code_relation_total M (E_kp_request (CEvar 1) (CEvar 2) (CEvar 4)) rho) as [r HR].
  destruct (code_relation_total M (E_kp_request (CEvar 1) (CEvar 2) (CEvar 5)) rho) as [rp HRP].
  destruct (code_relation_total M (E_weq (CEvar 0) (CEvar 3)) rho) as [h HH].
  assert (HEq : equality_graph M a p h).
  { exact (proj1 (expression_equality_graph M rho (CEvar 0) (CEvar 3) a p h eq_refl eq_refl) HH). }
  assert (HRA : named_binder_absent M r a).
  { apply (request_binder_absent M rho (CEvar 1) (CEvar 2) (CEvar 4) b a eq_refl HBA).
    - intros v HV. change (v=m) in HV. now subst v.
    - exact HR. }
  assert (HRPabs : named_binder_absent M r p).
  { apply (request_binder_absent M rho (CEvar 1) (CEvar 2) (CEvar 4) b p eq_refl HBP).
    - intros v HV. change (v=m) in HV. now subst v.
    - exact HR. }
  pose proof (request_input_substitution M a b k p m mp r rp HA HBA HBP HKA HM HR HRP) as HS.
  apply (proj2 (ns_under_expression M rho
    (E_weq (CEvar 0) (CEvar 3)) (E_kp_request (CEvar 1) (CEvar 2) (CEvar 4))
    (E_kp_request (CEvar 1) (CEvar 2) (CEvar 5)) h r rp HH HR HRP)).
  exact (proj1 (named_leibniz_internal M r a p h rp HEq HRA HRPabs HS)).
Qed.

Lemma request_conjunction_swap G p q :
  template_proof G (E_wim (E_wa p q) (E_wa q p)).
Proof.
  apply template_discharge,template_deduction,template_der_andi.
  - apply template_der_andr with (a:=p);apply dhyp;now left.
  - apply template_der_andl with (b:=q);apply dhyp;now left.
Qed.

Lemma request_existential_collapse G inputs x f :
  proof_macro G inputs (E_vac x f) ->
  proof_macro G inputs (E_wim (E_wex x f) f).
Proof.
  intro HV. eapply macro_syl;[apply macro_exists_monotone;exact HV|].
  apply PM_template,template_r6.
Qed.

Lemma request_from_raw_program G inputs b k m :
  proof_macro G inputs (E_vac b (E_wex b (E_wa m (E_wel b k)))) ->
  proof_macro G inputs (E_wim (E_krequest b k m) (E_kp_request b k m)).
Proof.
  intro HV. unfold E_krequest,E_kp_request.
  eapply macro_syl;[apply ns_macro_all_exists|].
  apply kp0_implication_map. eapply macro_syl.
  - apply request_existential_collapse;exact HV.
  - apply macro_exists_monotone,PM_template,request_conjunction_swap.
Qed.

Theorem numerical_raw_request M env b k m :
  ns_proof M env (E_wim (E_krequest b k m) (E_kp_request b k m)).
Proof.
  apply (ns_proof_macro M env (E_vac b (E_wex b (E_wa m (E_wel b k))) :: nil)).
  - intros e [<-|[]]. apply ns_bound_existential_vacuity.
  - apply request_from_raw_program,PM_input;now left.
Qed.

Definition E_kp_recursive a b k m :=
  E_wal b (E_wim (E_wel b k)
    (E_wal a (E_wim (E_ksubset a b k) (E_kp_request b k m)))).

Definition emitted_recursive_inputs a b k m :=
  E_vac a (E_wal a (E_wim (E_ksubset a b k) (E_krequest b k m))) ::
  E_vac b (E_wex b (E_wa m (E_wel b k))) :: nil.

Lemma emitted_recursive_program a b k m :
  proof_macro nil (emitted_recursive_inputs a b k m)
    (E_wim (E_kp_emitted a b k m) (E_kp_recursive a b k m)).
Proof.
  unfold E_kp_emitted,E_kp_recursive. apply macro_all_monotone,kp0_implication_map.
  eapply macro_syl.
  - eapply macro_syl;[apply macro_exists_monotone,PM_template,bootstrap_projection_right|].
    apply request_existential_collapse,PM_input;unfold emitted_recursive_inputs;now left.
  - apply macro_all_monotone,kp0_implication_map,request_from_raw_program,PM_input.
    unfold emitted_recursive_inputs;now right;left.
Qed.

Theorem numerical_emitted_recursive M env a b k m :
  ns_proof M env (E_wim (E_kp_emitted a b k m) (E_kp_recursive a b k m)).
Proof.
  apply (ns_proof_macro M env (emitted_recursive_inputs a b k m)).
  - intros e [<-|[<-|[]]].
    + apply ns_bound_universal_vacuity.
    + apply ns_bound_existential_vacuity.
  - apply emitted_recursive_program.
Qed.

Definition E_kp_recursive_seed a b k m :=
  E_wex k (E_wa (E_kp_request b k m) (E_kp_recursive a b k m)).

Theorem numerical_seed_recursive M env a b k m :
  ns_proof M env (E_wim (E_kp_seed_root a b k m) (E_kp_recursive_seed a b k m)).
Proof.
  apply (ns_proof_macro M env
    (E_wim (E_kp_emitted a b k m) (E_kp_recursive a b k m) :: nil)).
  - intros e [<-|[]]. apply numerical_emitted_recursive.
  - unfold E_kp_seed_root,E_kp_recursive_seed,E_kp_request.
    apply macro_exists_monotone,macro_discharge,macro_deduction,kp0_md_conjunction.
    + eapply md_mp with (a:=E_wa
        (E_wim (E_wex b m) (E_wex b (E_wa (E_wel b k) m))) (E_kp_emitted a b k m));
        [apply md_hyp;now left|].
      apply md_global,PM_template,bootstrap_projection_left.
    + eapply md_mp with (a:=E_kp_emitted a b k m).
      * eapply md_mp with (a:=E_wa
          (E_wim (E_wex b m) (E_wex b (E_wa (E_wel b k) m))) (E_kp_emitted a b k m));
          [apply md_hyp;now left|].
        apply md_global,PM_template,bootstrap_projection_right.
      * apply md_global,PM_input;now left.
Qed.

Theorem numerical_uniform_recursive_seed M a b m :
  exists k f, k<>a /\ k<>b /\ formula_fresh M m k /\
    code_relation M (code_parameters a b k m)
      (E_kp_recursive_seed (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)) f /\
    numerically_provable M f.
Proof.
  destruct (numerical_uniform_kp0_seed_unrestricted M a b m)
    as [k [seed [Hka [Hkb [HK [HS PS]]]]]].
  set (rho:=code_parameters a b k m).
  destruct (code_relation_total M
    (E_kp_recursive_seed (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)) rho) as [f HF].
  exists k,f. split;[exact Hka|]. split;[exact Hkb|]. split;[exact HK|].
  split;[exact HF|].
  apply (ns_proof_mp M rho (E_kp_seed_root (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3))
    (E_kp_recursive_seed (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)));[| |exact HF].
  - intros g HG. assert (g=seed) by exact (code_relation_functional M _ _ g seed HG HS).
    now subst g.
  - apply numerical_seed_recursive.
Qed.

Print Assumptions request_input_substitution.
Print Assumptions numerical_request_input_congruence.
Print Assumptions numerical_raw_request.
Print Assumptions numerical_emitted_recursive.
Print Assumptions numerical_seed_recursive.
Print Assumptions numerical_uniform_recursive_seed.
