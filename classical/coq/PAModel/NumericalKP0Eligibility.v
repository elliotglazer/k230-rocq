(** Capture-checked input specialization for the recursive request clause.
    The matrix code may be nonstandard. All substitution and binder
    hypotheses are explicit, and the output is a genuine numerical proof. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension CodeExpressions CodeDescent
  NumericalProofs NumericalEquality NumericalVacuitySteps ProofTemplates
  TemplatePropositional ProofMacros QuantifierMacros NamedLeibnizSteps
  NamedSubstitution NamedSubstitutionRules NamedBinderFresh NamedSpecialization
  TemplateBinderFresh TemplateNamedSubstitution NamedExistential NamedAlpha
  NumericalKP0 NumericalKP0Requests BoundVariableVacuityRules ContextualPropositional
  QuotientAtomTemplates NumericalBootstrap TemplateFormulaFresh NumericalVacuity FreshNames.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Definition E_recursive_at a b k m := E_wim (E_ksubset a b k) (E_kp_request b k m).

Theorem recursive_input_substitution M a b k p m mp q qp :
  a<>zeroM M -> b<>a -> b<>p -> k<>a -> k<>p ->
  named_substitution M m a p mp ->
  code_relation M (request_parameters M a b k p m mp)
    (E_recursive_at (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 4)) q ->
  code_relation M (request_parameters M a b k p m mp)
    (E_recursive_at (CEvar 3) (CEvar 1) (CEvar 2) (CEvar 5)) qp ->
  named_substitution M q a p qp.
Proof.
  intros HA HBA HBP HKA HKP HM HQ HQP.
  set (rho:=request_parameters M a b k p m mp).
  assert (HK : expression_named_replace M rho rho a p (CEvar 2) (CEvar 2)).
  { intros u v HU HV. change (u=k) in HU. change (v=k) in HV. subst u v. now right. }
  assert (HB : expression_named_replace M rho rho a p (CEvar 1) (CEvar 1)).
  { intros u v HU HV. change (u=b) in HU. change (v=b) in HV. subst u v. now right. }
  assert (HP : expression_named_replace M rho rho a p (CEvar 0) (CEvar 3)).
  { intros u v HU HV. change (u=a) in HU. change (v=p) in HV. subst u v. now left. }
  apply (expression_ns_implication M rho rho a p
    (E_ksubset (CEvar 0) (CEvar 1) (CEvar 2)) (E_kp_request (CEvar 1) (CEvar 2) (CEvar 4))
    (E_ksubset (CEvar 3) (CEvar 1) (CEvar 2)) (E_kp_request (CEvar 1) (CEvar 2) (CEvar 5))).
  - unfold E_ksubset.
    apply (expression_ns_universal M rho rho a p (CEvar 2) (CEvar 2) _ _ k
      eq_refl eq_refl HKA HKP).
    apply expression_ns_implication;apply (expression_ns_atom M rho rho a p false);assumption.
  - intros r rp HR HRP. exact (request_input_substitution M a b k p m mp r rp HA HBA HBP HKA HM HR HRP).
  - exact HQ.
  - exact HQP.
Qed.

Lemma recursive_binder_absent M rho A B K F b k name :
  code_relation M rho B b -> code_relation M rho K k -> b<>name -> k<>name ->
  expression_binder_absent M rho name F ->
  expression_binder_absent M rho name (E_recursive_at A B K F).
Proof.
  intros HB HK HBN HKN HF. unfold E_recursive_at. apply expression_binder_absent_implication.
  - unfold E_ksubset. apply expression_binder_absent_universal.
    + intros v HV. rewrite (code_relation_functional M K rho v k HV HK). exact HKN.
    + apply expression_binder_absent_implication;apply expression_binder_absent_atom;now left.
  - exact (request_binder_absent M rho B K F b name HB HBN HF).
Qed.

Theorem numerical_recursive_input_specialization M a b k p m mp :
  a<>zeroM M -> a<>p -> b<>a -> b<>p -> k<>a -> k<>p ->
  named_binder_absent M m a -> named_binder_absent M m p ->
  named_substitution M m a p mp ->
  ns_proof M (request_parameters M a b k p m mp)
    (E_wim (E_wal (CEvar 0) (E_recursive_at (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 4)))
      (E_recursive_at (CEvar 3) (CEvar 1) (CEvar 2) (CEvar 5))).
Proof.
  intros HA HAP HBA HBP HKA HKP HMA HMP HM result HResult.
  set (rho:=request_parameters M a b k p m mp).
  destruct (code_relation_total M (E_recursive_at (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 4)) rho)
    as [q HQ].
  destruct (code_relation_total M (E_recursive_at (CEvar 3) (CEvar 1) (CEvar 2) (CEvar 5)) rho)
    as [qp HQP].
  destruct (code_relation_total M (E_wal (CEvar 0)
    (E_recursive_at (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 4))) rho) as [allq HAll].
  assert (HQA : named_binder_absent M q a).
  { apply (recursive_binder_absent M rho (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 4)
      b k a eq_refl eq_refl HBA HKA).
    - intros v HV. change (v=m) in HV. now subst v.
    - exact HQ. }
  assert (HQPabs : named_binder_absent M q p).
  { apply (recursive_binder_absent M rho (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 4)
      b k p eq_refl eq_refl HBP HKP).
    - intros v HV. change (v=m) in HV. now subst v.
    - exact HQ. }
  apply (numerical_named_specialization M q a p qp allq result HAP HQA HQPabs).
  - exact (recursive_input_substitution M a b k p m mp q qp HA HBA HBP HKA HKP HM HQ HQP).
  - exact (expression_universal_graph M rho (CEvar 0)
      (E_recursive_at (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 4)) a q allq eq_refl HQ HAll).
  - exact (expression_implication_graph M rho
      (E_wal (CEvar 0) (E_recursive_at (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 4)))
      (E_recursive_at (CEvar 3) (CEvar 1) (CEvar 2) (CEvar 5)) allq qp result HAll HQP HResult).
Qed.

Definition E_kp_eligible a b k p :=
  E_or (E_weq a p) (E_wex b (E_wa (E_wel b k) (E_ksubset p b k))).

Lemma eligibility_curry G p q r :
  template_proof G (E_wim (E_wim p (E_wim q r)) (E_wim (E_wa p q) r)).
Proof.
  apply template_discharge. do 2 apply template_deduction.
  eapply dmp with (a:=q).
  - eapply dmp with (a:=p).
    + apply dhyp;cbn;tauto.
    + apply template_der_andl with (b:=q),dhyp;now left.
  - apply template_der_andr with (a:=p),dhyp;now left.
Qed.

Lemma eligibility_cases G inputs p q e r t :
  proof_macro G inputs (E_wim e (E_wim p t)) ->
  proof_macro G inputs (E_wim q (E_wim r t)) ->
  proof_macro G inputs (E_wim (E_wa p q) (E_wim (E_or e r) t)).
Proof.
  intros HE HR. apply macro_discharge. do 2 apply macro_deduction.
  eapply md_mp with (a:=E_or e r);[apply md_hyp;now left|].
  eapply md_mp with (a:=E_wim r t).
  - eapply md_mp with (a:=q).
    + eapply md_mp with (a:=E_wa p q);[apply md_hyp;cbn;tauto|].
      apply md_global,PM_template,bootstrap_projection_right.
    + apply md_global;exact HR.
  - eapply md_mp with (a:=E_wim e t).
    + apply macro_deduction. eapply md_mp with (a:=p).
      * eapply md_mp with (a:=E_wa p q);[apply md_hyp;cbn;tauto|].
        apply md_global,PM_template,bootstrap_projection_left.
      * eapply md_mp with (a:=e);[apply md_hyp;now left|]. apply md_global;exact HE.
    + apply md_global,PM_template,template_or_elimination.
Qed.

Definition eligibility_inputs a b k p m mp :=
  E_wim (E_wal a (E_recursive_at a b k m)) (E_recursive_at p b k mp) ::
  E_wim (E_weq a p) (E_wim (E_kp_request b k m) (E_kp_request b k mp)) ::
  E_vac b (E_kp_request b k mp) :: nil.

Lemma eligibility_program a b k p m mp :
  proof_macro nil (eligibility_inputs a b k p m mp)
    (E_wim (E_wa (E_kp_request b k m) (E_kp_recursive a b k m))
      (E_wim (E_kp_eligible a b k p) (E_kp_request b k mp))).
Proof.
  set (inputs:=eligibility_inputs a b k p m mp).
  assert (HR : proof_macro nil inputs
    (E_wim (E_kp_recursive a b k m)
      (E_wal b (E_wim (E_wa (E_wel b k) (E_ksubset p b k)) (E_kp_request b k mp))))).
  { unfold E_kp_recursive. eapply macro_syl.
    - apply macro_all_monotone,kp0_implication_map,PM_input.
      unfold inputs,eligibility_inputs;now left.
    - apply macro_all_monotone,PM_template,eligibility_curry. }
  assert (HR' : proof_macro nil inputs
    (E_wim (E_kp_recursive a b k m)
      (E_wim (E_wex b (E_wa (E_wel b k) (E_ksubset p b k))) (E_kp_request b k mp)))).
  { eapply macro_syl;[exact HR|].
    eapply macro_syl;[apply ns_macro_all_exists|].
    apply kp0_implication_map,request_existential_collapse,PM_input.
    unfold inputs,eligibility_inputs;now right;right;left. }
  unfold E_kp_eligible. apply eligibility_cases;[|exact HR'].
  apply PM_input. unfold inputs,eligibility_inputs;now right;left.
Qed.

Theorem numerical_request_bound_vacuity M rho B K F :
  ns_proof M rho (E_vac B (E_kp_request B K F)).
Proof.
  apply (ns_proof_macro M rho
    (E_vac B (E_wex B F) :: E_vac B (E_wex B (E_wa (E_wel B K) F)) :: nil)).
  - intros e [<-|[<-|[]]];apply ns_bound_existential_vacuity.
  - unfold E_kp_request. apply macro_vacuous_implication;apply PM_input;cbn;tauto.
Qed.

Theorem numerical_kp0_eligibility M a b k p m mp :
  a<>zeroM M -> a<>p -> b<>a -> b<>p -> k<>a -> k<>p ->
  named_binder_absent M m a -> named_binder_absent M m p ->
  named_substitution M m a p mp ->
  ns_proof M (request_parameters M a b k p m mp)
    (E_wim (E_wa (E_kp_request (CEvar 1) (CEvar 2) (CEvar 4))
      (E_kp_recursive (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 4)))
      (E_wim (E_kp_eligible (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3))
        (E_kp_request (CEvar 1) (CEvar 2) (CEvar 5)))).
Proof.
  intros HA HAP HBA HBP HKA HKP HMA HMP HM.
  apply (ns_proof_macro M (request_parameters M a b k p m mp)
    (eligibility_inputs (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5))).
  - intros e [<-|[<-|[<-|[]]]].
    + exact (numerical_recursive_input_specialization M a b k p m mp HA HAP HBA HBP HKA HKP HMA HMP HM).
    + exact (numerical_request_input_congruence M a b k p m mp HA HBA HBP HKA HMA HMP HM).
    + apply numerical_request_bound_vacuity.
  - apply eligibility_program.
Qed.

Lemma kp0_subset_fresh M rho name A B K :
  expression_name_avoids M rho name A -> expression_name_avoids M rho name B ->
  expression_name_avoids M rho name K -> expression_fresh M rho name (E_ksubset A B K).
Proof.
  intros HA HB HK. unfold E_ksubset. apply expression_fresh_universal;[exact HK|].
  apply expression_fresh_implication;apply expression_fresh_atom;try (now left);assumption.
Qed.

Lemma kp0_request_fresh M rho name B K F : name<>zeroM M ->
  expression_name_avoids M rho name B -> expression_name_avoids M rho name K ->
  expression_fresh M rho name F -> expression_fresh M rho name (E_kp_request B K F).
Proof.
  intros HN HB HK HF. unfold E_kp_request. apply expression_fresh_implication.
  - apply expression_fresh_existential;assumption.
  - apply expression_fresh_existential;[exact HN|exact HB|].
    apply expression_fresh_conjunction;[exact HN| |exact HF].
    apply expression_fresh_atom;[now left|exact HB|exact HK].
Qed.

Lemma kp0_recursive_fresh M rho name A B K F : name<>zeroM M ->
  expression_name_avoids M rho name A -> expression_name_avoids M rho name B ->
  expression_name_avoids M rho name K -> expression_fresh M rho name F ->
  expression_fresh M rho name (E_kp_recursive A B K F).
Proof.
  intros HN HA HB HK HF. unfold E_kp_recursive.
  apply expression_fresh_universal;[exact HB|]. apply expression_fresh_implication.
  - apply expression_fresh_atom;[now left|exact HB|exact HK].
  - apply expression_fresh_universal;[exact HA|]. apply expression_fresh_implication.
    + apply kp0_subset_fresh;assumption.
    + apply kp0_request_fresh;assumption.
Qed.

Lemma kp0_expression_fresh_vacuity M rho X F x :
  code_relation M rho X x -> expression_fresh M rho x F ->
  ns_proof M rho (E_vac X F).
Proof.
  intros HX HF result HR. destruct (code_relation_total M F rho) as [f Hf].
  apply (numerical_vacuity M x f result (HF f Hf)).
  exact (proj1 (expression_vacuity_graph M rho X F x f result HX Hf) HR).
Qed.

Theorem numerical_kp0_quantified_request M a b k p m mp :
  a<>zeroM M -> a<>p -> b<>a -> b<>p -> k<>a -> k<>p -> p<>zeroM M ->
  named_binder_absent M m a -> formula_fresh M m p -> named_substitution M m a p mp ->
  ns_proof M (request_parameters M a b k p m mp)
    (E_wim (E_wa (E_kp_request (CEvar 1) (CEvar 2) (CEvar 4))
      (E_kp_recursive (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 4)))
      (E_wal (CEvar 3) (E_wim (E_kp_eligible (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3))
        (E_kp_request (CEvar 1) (CEvar 2) (CEvar 5))))).
Proof.
  intros HA HAP HBA HBP HKA HKP HP HMA HMP HM.
  set (rho:=request_parameters M a b k p m mp).
  set (F:=E_wa (E_kp_request (CEvar 1) (CEvar 2) (CEvar 4))
    (E_kp_recursive (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 4))).
  set (G:=E_wim (E_kp_eligible (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3))
    (E_kp_request (CEvar 1) (CEvar 2) (CEvar 5))).
  assert (EF : expression_fresh M rho p F).
  { assert (EA : expression_name_avoids M rho p (CEvar 0))
      by (intros v Hv;change (v=a) in Hv;now subst v).
    assert (EB : expression_name_avoids M rho p (CEvar 1))
      by (intros v Hv;change (v=b) in Hv;now subst v).
    assert (EK : expression_name_avoids M rho p (CEvar 2))
      by (intros v Hv;change (v=k) in Hv;now subst v).
    assert (EM : expression_fresh M rho p (CEvar 4))
      by (intros v Hv;change (v=m) in Hv;now subst v).
    unfold F. apply expression_fresh_conjunction;[exact HP| |].
    - apply kp0_request_fresh;assumption.
    - apply kp0_recursive_fresh;assumption. }
  apply (ns_proof_macro M rho (E_wim F G :: E_vac (CEvar 3) F :: nil)).
  - intros e [<-|[<-|[]]].
    + exact (numerical_kp0_eligibility M a b k p m mp HA HAP HBA HBP HKA HKP HMA
        (named_formula_fresh_binder_absent M m p HMP) HM).
    + exact (kp0_expression_fresh_vacuity M rho (CEvar 3) F p eq_refl EF).
  - eapply macro_syl;[apply PM_input;now right;left|].
    apply macro_all_monotone,PM_input;now left.
Qed.

Definition E_kp_support_body a b k m :=
  E_wal b (E_wim (E_wel b k) (E_wex a m)).
Definition E_kp_conclusion a b k p m mp :=
  E_wex k (E_wa (E_wal p (E_wim (E_kp_eligible a b k p) (E_kp_request b k mp)))
    (E_kp_support_body a b k m)).

Theorem numerical_emitted_support M rho a b k m :
  ns_proof M rho (E_wim (E_kp_emitted a b k m) (E_kp_support_body a b k m)).
Proof.
  apply (ns_proof_macro M rho nil);[intros e []|].
  unfold E_kp_emitted,E_kp_support_body.
  apply macro_all_monotone,kp0_implication_map,macro_exists_monotone.
  apply PM_template,bootstrap_projection_left.
Qed.

Lemma kp0_full_program a b k p m mp :
  proof_macro nil
    (E_wim (E_wa (E_kp_request b k m) (E_kp_recursive a b k m))
      (E_wal p (E_wim (E_kp_eligible a b k p) (E_kp_request b k mp))) ::
     E_wim (E_kp_emitted a b k m) (E_kp_recursive a b k m) ::
     E_wim (E_kp_emitted a b k m) (E_kp_support_body a b k m) :: nil)
    (E_wim (E_kp_seed_root a b k m) (E_kp_conclusion a b k p m mp)).
Proof.
  unfold E_kp_seed_root,E_kp_conclusion.
  apply macro_exists_monotone,macro_discharge,macro_deduction,kp0_md_conjunction.
  - eapply md_mp with (a:=E_wa (E_kp_request b k m) (E_kp_recursive a b k m)).
    + apply kp0_md_conjunction.
      * eapply md_mp;[apply md_hyp;now left|].
        apply md_global,PM_template,bootstrap_projection_left.
      * eapply md_mp with (a:=E_kp_emitted a b k m).
        -- eapply md_mp;[apply md_hyp;now left|].
           apply md_global,PM_template,bootstrap_projection_right.
        -- apply md_global,PM_input;cbn;tauto.
    + apply md_global,PM_input;now left.
  - eapply md_mp with (a:=E_kp_emitted a b k m).
    + eapply md_mp;[apply md_hyp;now left|].
      apply md_global,PM_template,bootstrap_projection_right.
    + apply md_global,PM_input;cbn;tauto.
Qed.

Theorem numerical_kp0_from_seed M a b k p m mp :
  a<>zeroM M -> a<>p -> b<>a -> b<>p -> k<>a -> k<>p -> p<>zeroM M ->
  named_binder_absent M m a -> formula_fresh M m p -> named_substitution M m a p mp ->
  ns_proof M (request_parameters M a b k p m mp)
    (E_wim (E_kp_seed_root (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 4))
      (E_kp_conclusion (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5))).
Proof.
  intros HA HAP HBA HBP HKA HKP HP HMA HMP HM.
  eapply ns_proof_macro;[|apply kp0_full_program].
  intros e [<-|[<-|[<-|[]]]].
  - exact (numerical_kp0_quantified_request M a b k p m mp HA HAP HBA HBP HKA HKP HP HMA HMP HM).
  - apply numerical_emitted_recursive.
  - apply numerical_emitted_support.
Qed.

Lemma kp0_fresh_input_name M a b k m :
  exists p, a<>p /\ b<>p /\ k<>p /\ p<>zeroM M /\ formula_fresh M m p.
Proof.
  set (t:=succM M (addM M a b)).
  set (u:=succM M (addM M t k)).
  set (p:=succM M (addM M u m)).
  assert (HAT : coding_lt M a t) by (unfold t;apply coding_le_add).
  assert (HBT : coding_lt M b t).
  { unfold t. rewrite Arithmetic.add_comm. apply coding_le_add. }
  assert (HTU : coding_lt M t u) by (unfold u;apply coding_le_add).
  assert (HKU : coding_lt M k u).
  { unfold u. rewrite Arithmetic.add_comm. apply coding_le_add. }
  assert (HUP : coding_lt M u p) by (unfold p;apply coding_le_add).
  assert (HMP : coding_lt M m p).
  { unfold p. rewrite Arithmetic.add_comm. apply coding_le_add. }
  assert (HAP : coding_lt M a p) by
    exact (coding_lt_trans M a t p HAT (coding_lt_trans M t u p HTU HUP)).
  assert (HBP : coding_lt M b p) by
    exact (coding_lt_trans M b t p HBT (coding_lt_trans M t u p HTU HUP)).
  assert (HKP : coding_lt M k p) by exact (coding_lt_trans M k u p HKU HUP).
  exists p. split.
  - exact (@Peano.lt_neq (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) a p HAP).
  - split.
    + exact (@Peano.lt_neq (carrier M) (raw_interpretation M)
        (fun ax H rho=>axioms M ax rho H) b p HBP).
    + split.
      * exact (@Peano.lt_neq (carrier M) (raw_interpretation M)
          (fun ax H rho=>axioms M ax rho H) k p HKP).
      * split.
        -- intro E. apply (@Peano.lt_neq (carrier M) (raw_interpretation M)
             (fun ax H rho=>axioms M ax rho H) (zeroM M) p
             (coding_zero_lt_succ M (addM M u m))). symmetry;exact E.
        -- exact (formula_above_is_fresh M m p HMP).
Qed.

Theorem numerical_uniform_kp0 M a b m :
  a<>zeroM M -> b<>a -> named_binder_absent M m a ->
  exists k p mp f, k<>a /\ k<>b /\ a<>p /\ b<>p /\ k<>p /\ p<>zeroM M /\
    formula_fresh M m k /\ formula_fresh M m p /\ named_substitution M m a p mp /\
    code_relation M (request_parameters M a b k p m mp)
      (E_kp_conclusion (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)) f /\
    numerically_provable M f.
Proof.
  intros HA HBA HMA.
  destruct (numerical_uniform_kp0_seed_unrestricted M a b m)
    as [k [seed [HKA [HKB [HMK [HS PS]]]]]].
  destruct (kp0_fresh_input_name M a b k m) as [p [HAP [HBP [HKP [HP HMP]]]]].
  destruct (named_substitution_binder_absent_total M m a p
    (named_formula_fresh_binder_absent M m p HMP)) as [mp HM].
  set (rho:=request_parameters M a b k p m mp).
  destruct (code_relation_total M (E_kp_conclusion
    (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)) rho) as [f HF].
  assert (HSeed : code_relation M rho
    (E_kp_seed_root (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 4)) seed) by exact HS.
  assert (PF : numerically_provable M f).
  { apply (ns_proof_mp M rho
      (E_kp_seed_root (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 4))
      (E_kp_conclusion (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)));[| |exact HF].
    - intros s Hs. assert (s=seed) by exact (code_relation_functional M _ _ s seed Hs HSeed).
      now subst s.
    - exact (numerical_kp0_from_seed M a b k p m mp HA HAP HBA HBP HKA HKP HP HMA HMP HM). }
  exists k,p,mp,f. split;[exact HKA|]. split;[exact HKB|]. split;[exact HAP|].
  split;[exact HBP|]. split;[exact HKP|]. split;[exact HP|]. split;[exact HMK|].
  split;[exact HMP|]. split;[exact HM|]. split;assumption.
Qed.

Print Assumptions recursive_input_substitution.
Print Assumptions numerical_recursive_input_specialization.
Print Assumptions numerical_kp0_eligibility.
Print Assumptions numerical_kp0_quantified_request.
Print Assumptions numerical_kp0_from_seed.
Print Assumptions numerical_uniform_kp0.
