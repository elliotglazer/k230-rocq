(** Linking binder-policy compilation to the checked finite-plan alpha theorem.
    The formula is host-finite; all free names and assigned binders may be
    elements of an arbitrary PA model. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates
  NamedLeibnizSteps NumericalEquivalence FiniteNamedPolicies FiniteNamedPlans FiniteTemplateEvaluation
  TemplateBinderFresh TemplateNamedExclusions FiniteTemplateRebase
  QuotientAtomTemplates QuotationPayloads SetFormulaCodes.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Fixpoint policy_plan_graph M rho (policy : named_binder_policy) fresh {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff)
  (p : finite_binder_plan M) : Prop :=
  match phi,p with
  | falsity,PlanLeaf => True
  | atom _ _,PlanLeaf => True
  | bin _ a b,PlanBinary pa pb =>
      policy_plan_graph M rho policy fresh a pa /\ policy_plan_graph M rho policy fresh b pb
  | quant _ a,PlanBind x pa =>
      code_relation M rho (policy fresh (named_policy_depth a)) x /\
      policy_plan_graph M rho policy (CEadd fresh (CEconst 1)) a pa
  | _,_ => False
  end.
Definition policy_hygienic M rho eta policy fresh {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) :=
  exists p,policy_plan_graph M rho policy fresh phi p /\ plan_hygienic M eta p.

Theorem policy_plan_total M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) :
  forall rho policy fresh,exists p,policy_plan_graph M rho policy fresh phi p.
Proof.
  induction phi as [|fl P ts|fl op a IHa b IHb|fl q a IH];intros rho policy fresh.
  - exists PlanLeaf. exact I.
  - exists PlanLeaf. exact I.
  - destruct (IHa rho policy fresh) as [pa HA],(IHb rho policy fresh) as [pb HB].
    exists (PlanBinary pa pb). split;assumption.
  - destruct (code_relation_total M (policy fresh (named_policy_depth a)) rho) as [x HX].
    destruct (IH rho policy (CEadd fresh (CEconst 1))) as [pa HA].
    exists (PlanBind x pa). split;assumption.
Qed.

Theorem policy_plan_evaluation_graph M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) :
  forall rho policy fresh p env eta f,
    policy_plan_graph M rho policy fresh phi p ->
    (forall i,code_relation M rho (env i) (eta i)) ->
    (code_relation M rho (named_policy_formula false (CEconst 1) policy env fresh phi) f <->
      named_plan_evaluation M phi eta p f).
Proof.
  induction phi as [|fl P ts|fl op a IHa b IHb|fl q a IH];
    intros rho policy fresh p env eta f HP HE;
    destruct p as [|pa pb|x pa];cbn [policy_plan_graph] in HP;try contradiction.
  - reflexivity.
  - cbn [named_plan_evaluation named_policy_formula]. destruct P.
    + exact (ns_atom_expression M rho false _ _ _ _ f
        (template_term_graph M rho env eta _ HE) (template_term_graph M rho env eta _ HE)).
    + exact (ns_atom_expression M rho true _ _ _ _ f
        (template_term_graph M rho env eta _ HE) (template_term_graph M rho env eta _ HE)).
  - destruct HP as [HPA HPB]. cbn [named_plan_evaluation].
    set (A:=named_policy_formula false (CEconst 1) policy env fresh a).
    set (B:=named_policy_formula false (CEconst 1) policy env fresh b).
    assert (EQ : named_policy_formula false (CEconst 1) policy env fresh (bin op a b) =
      match op with Conj=>E_wa A B|Disj=>E_or A B|Impl=>E_wim A B end).
    { destruct op;reflexivity. }
    rewrite EQ. split.
    + intro HF. destruct (code_relation_total M A rho) as [u HU].
      destruct (code_relation_total M B rho) as [v HV]. exists u,v.
      split;[exact (proj1 (IHa rho policy fresh pa env eta u HPA HE) HU)|].
      split;[exact (proj1 (IHb rho policy fresh pb env eta v HPB HE) HV)|].
      exact (proj1 (template_binary_graph M rho op A B u v f HU HV) HF).
    + intros [u [v [HU [HV HF]]]].
      exact (proj2 (template_binary_graph M rho op A B u v f
        (proj2 (IHa rho policy fresh pa env eta u HPA HE) HU)
        (proj2 (IHb rho policy fresh pb env eta v HPB HE) HV)) HF).
  - destruct HP as [HX HPA].
    set (X:=policy fresh (named_policy_depth a)).
    set (A:=named_policy_formula false (CEconst 1) policy (X .: env)
      (CEadd fresh (CEconst 1)) a).
    assert (HE' : forall i,code_relation M rho ((X .: env) i) ((x .: eta) i)).
    { intros [|i];[exact HX|apply HE]. }
    assert (EQ : named_policy_formula false (CEconst 1) policy env fresh (quant q a) =
      if match q with All=>true|Ex=>false end then E_wal X A else E_wex X A).
    { destruct q;reflexivity. }
    rewrite EQ. cbn [named_plan_evaluation]. split.
    + intro HF. destruct (code_relation_total M A rho) as [u HU]. exists u. split.
      * exact (proj1 (IH rho policy (CEadd fresh (CEconst 1)) pa (X .: env)
          (x .: eta) u HPA HE') HU).
      * exact (proj1 (template_quantified_graph M rho (match q with All=>true|Ex=>false end)
          X A x u f HX HU) HF).
    + intros [u [HU HF]].
      exact (proj2 (template_quantified_graph M rho (match q with All=>true|Ex=>false end)
        X A x u f HX
        (proj2 (IH rho policy (CEadd fresh (CEconst 1)) pa (X .: env)
          (x .: eta) u HPA HE') HU)) HF).
Qed.

Theorem finite_policy_alpha_codes M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff)
  rho sigma policy policy' env env' fresh fresh' eta f g :
  (forall i,code_relation M rho (env i) (eta i)) ->
  (forall i,code_relation M sigma (env' i) (eta i)) ->
  policy_hygienic M rho eta policy fresh phi ->
  policy_hygienic M sigma eta policy' fresh' phi ->
  code_relation M rho (named_policy_formula false (CEconst 1) policy env fresh phi) f ->
  code_relation M sigma (named_policy_formula false (CEconst 1) policy' env' fresh' phi) g ->
  numerical_equivalent M f g.
Proof.
  intros HE HE' [p [HP HH]] [q [HQ HH']] HF HG.
  apply (finite_named_plan_alpha M phi eta p q f g HH HH').
  - exact (proj1 (policy_plan_evaluation_graph M phi rho policy fresh p env eta f HP HE) HF).
  - exact (proj1 (policy_plan_evaluation_graph M phi sigma policy' fresh' q env' eta g HQ HE') HG).
Qed.

Theorem finite_policy_bottom_alpha_codes M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff)
  rho sigma legacy policy policy' env env' fresh fresh' bottom_name eta f g :
  (forall i,code_relation M rho (env i) (eta i)) ->
  (forall i,code_relation M sigma (env' i) (eta i)) ->
  policy_hygienic M rho eta policy fresh phi ->
  policy_hygienic M sigma eta policy' fresh' phi ->
  code_relation M rho (named_policy_formula legacy (named_bottom_expression bottom_name)
    policy env fresh phi) f ->
  code_relation M sigma (named_policy_formula false (CEconst 1) policy' env' fresh' phi) g ->
  numerical_equivalent M f g.
Proof.
  intros HE HE' HP HQ HF HG.
  destruct (code_relation_total M (named_policy_formula false (CEconst 1) policy env fresh phi) rho)
    as [h HH].
  apply (numerical_equivalent_trans M f h g).
  - exact (named_policy_normalization_codes M rho phi legacy policy env fresh bottom_name f h HF HH).
  - exact (finite_policy_alpha_codes M phi rho sigma policy policy' env env' fresh fresh' eta h g
      HE HE' HP HQ HH HG).
Qed.

Theorem finite_policy_bottom_alpha_proof M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff)
  rho sigma legacy policy policy' env env' fresh fresh' bottom_name eta :
  (forall i,code_relation M rho (env i) (eta i)) ->
  (forall i,code_relation M sigma (env' i) (eta i)) ->
  policy_hygienic M rho eta policy fresh phi ->
  policy_hygienic M sigma eta policy' fresh' phi ->
  ns_proof M rho (named_policy_formula legacy (named_bottom_expression bottom_name)
    policy env fresh phi) ->
  ns_proof M sigma (named_policy_formula false (CEconst 1) policy' env' fresh' phi).
Proof.
  intros HE HE' HP HQ Hproof g HG.
  destruct (code_relation_total M (named_policy_formula legacy (named_bottom_expression bottom_name)
    policy env fresh phi) rho) as [f HF].
  apply (numerical_implies_apply M f g);[|exact (Hproof f HF)].
  exact (proj1 (finite_policy_bottom_alpha_codes M phi rho sigma legacy policy policy'
    env env' fresh fresh' bottom_name eta f g HE HE' HP HQ HF HG)).
Qed.

Print Assumptions policy_plan_total.
Print Assumptions policy_plan_evaluation_graph.
Print Assumptions finite_policy_alpha_codes.
Print Assumptions finite_policy_bottom_alpha_codes.
Print Assumptions finite_policy_bottom_alpha_proof.
