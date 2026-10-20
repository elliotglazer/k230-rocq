(** Unused free-name entries are irrelevant to finite policy normalization.
    This permits an old odd-index environment to be replaced by a bounded
    environment before testing hygiene of the increasing binder allocator. *)
From PAModel Require Import Model CodeDescent CodeExpressions NumericalProofs NumericalEquivalence
  FiniteNamedPolicies FiniteNamedPlans FinitePolicyAlpha FinitePolicyHygiene
  SourceBoundedCalibration SetFormulaCodes FiniteTemplateRebase QuotientAtomTemplates.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Lemma bounded_atom_agreement M tag a b a' b' f :
  @Logic.eq (carrier M) a a' -> @Logic.eq (carrier M) b b' ->
  (tagged_pair_graph M tag a b f <-> tagged_pair_graph M tag a' b' f).
Proof. intros -> ->. reflexivity. Qed.

Theorem named_plan_bounded_environment M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) :
  forall n, bounded n phi -> forall (eta eta' : nat -> carrier M) p f,
    (forall i,i<n -> @Logic.eq (carrier M) (eta i) (eta' i)) ->
    (named_plan_evaluation M phi eta p f <-> named_plan_evaluation M phi eta' p f).
Proof.
  induction phi as [|fl P ts|fl op a IHa b IHb|fl q a IH];
    intros n HB eta eta' p f HE;destruct p as [|pa pb|x pa];
    cbn [named_plan_evaluation];try reflexivity.
  - destruct P;apply sb_atom_bounded in HB;destruct HB as [Hone Htwo];
      apply bounded_atom_agreement;apply HE;assumption.
  - assert (HA : bounded n a) by (revert HB;invert_bounds;auto).
    assert (HC : bounded n b) by (revert HB;invert_bounds;auto).
    split;intros [u [v [HU [HV HF]]]];exists u,v;repeat split;try exact HF.
    + exact (proj1 (IHa n HA eta eta' pa u HE) HU).
    + exact (proj1 (IHb n HC eta eta' pb v HE) HV).
    + exact (proj2 (IHa n HA eta eta' pa u HE) HU).
    + exact (proj2 (IHb n HC eta eta' pb v HE) HV).
  - assert (HA : bounded (S n) a) by (revert HB;invert_bounds;auto).
    assert (HE' : forall i,i<S n -> @Logic.eq (carrier M) ((x .: eta) i) ((x .: eta') i)).
    { intros [|i] Hi;cbn;[reflexivity|apply HE;lia]. }
    split;intros [v [HV HF]];exists v;split;try exact HF.
    + exact (proj1 (IH (S n) HA (x .: eta) (x .: eta') pa v HE') HV).
    + exact (proj2 (IH (S n) HA (x .: eta) (x .: eta') pa v HE') HV).
Qed.

Theorem finite_policy_bounded_alpha_codes M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff)
  n rho sigma policy policy' env env' fresh fresh' eta eta' f g :
  bounded n phi -> (forall i,i<n -> @Logic.eq (carrier M) (eta i) (eta' i)) ->
  (forall i,code_relation M rho (env i) (eta i)) ->
  (forall i,code_relation M sigma (env' i) (eta' i)) ->
  policy_hygienic M rho eta' policy fresh phi ->
  policy_hygienic M sigma eta' policy' fresh' phi ->
  code_relation M rho (named_policy_formula false (CEconst 1) policy env fresh phi) f ->
  code_relation M sigma (named_policy_formula false (CEconst 1) policy' env' fresh' phi) g ->
  numerical_equivalent M f g.
Proof.
  intros HB HE HE1 HE2 [p [HP HH]] [q [HQ HH']] HF HG.
  apply (finite_named_plan_alpha M phi eta' p q f g HH HH').
  - apply (proj1 (named_plan_bounded_environment M phi n HB eta eta' p f HE)).
    exact (proj1 (policy_plan_evaluation_graph M phi rho policy fresh p env eta f HP HE1) HF).
  - exact (proj1 (policy_plan_evaluation_graph M phi sigma policy' fresh' q env' eta' g HQ HE2) HG).
Qed.

Theorem finite_policy_bounded_bottom_alpha_codes M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff)
  n rho sigma legacy policy policy' env env' fresh fresh' bottom_name eta eta' f g :
  bounded n phi -> (forall i,i<n -> @Logic.eq (carrier M) (eta i) (eta' i)) ->
  (forall i,code_relation M rho (env i) (eta i)) ->
  (forall i,code_relation M sigma (env' i) (eta' i)) ->
  policy_hygienic M rho eta' policy fresh phi ->
  policy_hygienic M sigma eta' policy' fresh' phi ->
  code_relation M rho (named_policy_formula legacy (named_bottom_expression bottom_name)
    policy env fresh phi) f ->
  code_relation M sigma (named_policy_formula false (CEconst 1) policy' env' fresh' phi) g ->
  numerical_equivalent M f g.
Proof.
  intros HB HE HE1 HE2 HP HQ HF HG.
  destruct (code_relation_total M (named_policy_formula false (CEconst 1) policy env fresh phi) rho)
    as [h HH].
  apply (numerical_equivalent_trans M f h g).
  - exact (named_policy_normalization_codes M rho phi legacy policy env fresh bottom_name f h HF HH).
  - exact (finite_policy_bounded_alpha_codes M phi n rho sigma policy policy' env env' fresh fresh'
      eta eta' h g HB HE HE1 HE2 HP HQ HH HG).
Qed.

Theorem finite_bounded_depth_to_sequential_codes M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff)
  n rho sigma legacy env env' oldfresh fresh bottom_name eta eta' k f g :
  bounded n phi -> (forall i,i<n -> @Logic.eq (carrier M) (eta i) (eta' i)) ->
  (forall i,code_relation M rho (env i) (eta i)) ->
  (forall i,code_relation M sigma (env' i) (eta' i)) ->
  (forall i m,1<=m<=named_policy_depth phi -> code_numeral M (2*m)<>eta' i) ->
  code_relation M sigma fresh k -> template_hygienic M phi eta' k ->
  code_relation M rho (named_policy_formula legacy (named_bottom_expression bottom_name)
    depth_binder_policy env oldfresh phi) f ->
  code_relation M sigma (template_set_formula env' fresh phi) g ->
  numerical_equivalent M f g.
Proof.
  intros HB HE HE1 HE2 HD HK HT HF HG. rewrite <- sequential_policy_exact in HG.
  apply (finite_policy_bounded_bottom_alpha_codes M phi n rho sigma legacy
    depth_binder_policy sequential_binder_policy env env' oldfresh fresh bottom_name eta eta' f g);
    try assumption.
  - now apply depth_policy_hygienic.
  - exact (sequential_policy_hygienic M phi sigma eta' fresh k HK HT).
Qed.

Print Assumptions named_plan_bounded_environment.
Print Assumptions finite_policy_bounded_alpha_codes.
Print Assumptions finite_policy_bounded_bottom_alpha_codes.
Print Assumptions finite_bounded_depth_to_sequential_codes.
