(** Concrete hygiene and alpha-normalization for the two binder policies:
    descending even names determined by body depth, and increasing names
    beginning at a chosen model-valued base. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
  NumericalEquivalence FiniteNamedPolicies FiniteNamedPlans FinitePolicyAlpha
  FiniteTemplateRebase TemplateNamedExclusions TemplateBinderFresh TargetNumeralLift QuotientAtomTemplates.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lia Arith.PeanoNat.
Unset Implicit Arguments.

Fixpoint depth_policy_plan M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) : finite_binder_plan M :=
  match phi with
  | falsity=>PlanLeaf|atom _ _=>PlanLeaf
  | bin _ a b=>PlanBinary (depth_policy_plan M a) (depth_policy_plan M b)
  | quant _ a=>PlanBind (code_numeral M (2 * named_policy_depth a + 2)) (depth_policy_plan M a)
  end.

Lemma depth_policy_plan_graph M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) :
  forall rho fresh,policy_plan_graph M rho depth_binder_policy fresh phi (depth_policy_plan M phi).
Proof.
  induction phi;intros rho fresh;cbn [policy_plan_graph depth_policy_plan depth_binder_policy].
  - exact I.
  - exact I.
  - split;[apply IHphi1|apply IHphi2].
  - split;[reflexivity|apply IHphi].
Qed.

Lemma depth_policy_plan_avoids M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) :
  forall y,(forall n,1<=n<=named_policy_depth phi -> code_numeral M (2*n)<>y) ->
    plan_avoids M (depth_policy_plan M phi) y.
Proof.
  induction phi;intros y HY;cbn [plan_avoids depth_policy_plan];try exact I.
  - split;[apply IHphi1|apply IHphi2];intros n Hn;apply HY;
      cbn [named_policy_depth] in *;lia.
  - split.
    + replace (2*named_policy_depth phi+2) with (2*S(named_policy_depth phi)) by lia.
      apply HY. cbn [named_policy_depth]. lia.
    + apply IHphi. intros n Hn. apply HY. cbn [named_policy_depth]. lia.
Qed.

Lemma depth_policy_plan_proper M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) :
  plan_proper M (depth_policy_plan M phi).
Proof.
  induction phi;cbn [plan_proper depth_policy_plan];try exact I.
  - split;assumption.
  - split.
    + change (code_numeral M (2*named_policy_depth phi+2)<>code_numeral M 0).
      apply target_numerals_distinct. lia.
    + split;[|exact IHphi]. apply depth_policy_plan_avoids.
      intros n Hn. apply target_numerals_distinct. lia.
Qed.

Lemma depth_policy_hygienic M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) rho eta fresh :
  (forall i n,1<=n<=named_policy_depth phi -> code_numeral M (2*n)<>eta i) ->
  policy_hygienic M rho eta depth_binder_policy fresh phi.
Proof.
  intro HE. exists (depth_policy_plan M phi). split;[apply depth_policy_plan_graph|].
  split;[apply depth_policy_plan_proper|]. intro i. apply depth_policy_plan_avoids,HE.
Qed.

Corollary depth_policy_odd_environment M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) rho fresh env :
  policy_hygienic M rho (fun j : nat => code_numeral M (2 * env j + 1)) depth_binder_policy fresh phi.
Proof. apply depth_policy_hygienic. intros i n Hn. apply target_numerals_distinct. lia. Qed.

Fixpoint sequential_policy_plan M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) k : finite_binder_plan M :=
  match phi with
  | falsity=>PlanLeaf|atom _ _=>PlanLeaf
  | bin _ a b=>PlanBinary (sequential_policy_plan M a k) (sequential_policy_plan M b k)
  | quant _ a=>PlanBind k (sequential_policy_plan M a (succM M k))
  end.

Lemma sequential_policy_plan_graph M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) :
  forall rho fresh k,code_relation M rho fresh k ->
    policy_plan_graph M rho sequential_binder_policy fresh phi (sequential_policy_plan M phi k).
Proof.
  induction phi;intros rho fresh k HK;
    cbn [policy_plan_graph sequential_policy_plan sequential_binder_policy].
  - exact I.
  - exact I.
  - split;[now apply IHphi1|now apply IHphi2].
  - split;[exact HK|apply IHphi;now apply template_fresh_increment_graph].
Qed.

Lemma sequential_policy_plan_avoids M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) :
  forall k y,template_allocations_avoid M phi k y ->
    plan_avoids M (sequential_policy_plan M phi k) y.
Proof.
  induction phi;intros k y HY;cbn [plan_avoids sequential_policy_plan];try exact I.
  - destruct HY as [HA HB]. split;[now apply IHphi1|now apply IHphi2].
  - destruct HY as [Hk HY]. split;[exact Hk|now apply IHphi].
Qed.

Lemma sequential_policy_plan_proper M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) :
  forall k,template_allocations_avoid M phi k (zeroM M) ->
    plan_proper M (sequential_policy_plan M phi k).
Proof.
  induction phi;intros k HK;cbn [plan_proper sequential_policy_plan];try exact I.
  - destruct HK as [HA HB]. split;[now apply IHphi1|now apply IHphi2].
  - destruct HK as [Hk HK]. split;[exact Hk|]. split.
    + apply sequential_policy_plan_avoids,template_allocations_avoid_below,coding_lt_succ.
    + now apply IHphi.
Qed.

Lemma sequential_policy_hygienic M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) rho eta fresh k :
  code_relation M rho fresh k -> template_hygienic M phi eta k ->
  policy_hygienic M rho eta sequential_binder_policy fresh phi.
Proof.
  intros HK [Hzero HE]. exists (sequential_policy_plan M phi k). split.
  - now apply sequential_policy_plan_graph.
  - split;[now apply sequential_policy_plan_proper|].
    intro i. apply sequential_policy_plan_avoids,HE.
Qed.

Theorem finite_depth_to_sequential_codes M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff)
  rho sigma legacy env env' oldfresh fresh bottom_name eta k f g :
  (forall i,code_relation M rho (env i) (eta i)) ->
  (forall i,code_relation M sigma (env' i) (eta i)) ->
  (forall i n,1<=n<=named_policy_depth phi -> code_numeral M (2*n)<>eta i) ->
  code_relation M sigma fresh k -> template_hygienic M phi eta k ->
  code_relation M rho (named_policy_formula legacy (named_bottom_expression bottom_name)
    depth_binder_policy env oldfresh phi) f ->
  code_relation M sigma (template_set_formula env' fresh phi) g ->
  numerical_equivalent M f g.
Proof.
  intros HE HE' HD HK HH HF HG. rewrite <- sequential_policy_exact in HG.
  apply (finite_policy_bottom_alpha_codes M phi rho sigma legacy
    depth_binder_policy sequential_binder_policy env env' oldfresh fresh bottom_name eta f g);
    try assumption.
  - now apply depth_policy_hygienic.
  - exact (sequential_policy_hygienic M phi sigma eta fresh k HK HH).
Qed.

Print Assumptions depth_policy_plan_proper.
Print Assumptions depth_policy_odd_environment.
Print Assumptions sequential_policy_hygienic.
Print Assumptions finite_depth_to_sequential_codes.
