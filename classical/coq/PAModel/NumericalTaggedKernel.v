(** Actual construction of one container with every tagged request and
    the exact upper containment profile. Witness introduction remains a
    separate step toward the two directions of tagged comprehension. *)
From PAModel Require Import Model FiniteCoding CodeExpressions CodeDescent
  NumericalProofs ProofTemplates NamedLeibnizSteps FreshNames NamedBinderFresh
  TemplateFormulaFresh TemplatePropositional ProofMacros QuantifierMacros
  NumericalKP0 NumericalKP0Requests NumericalKP0Eligibility NumericalSingleton
  NumericalTaggedComprehension NumericalTaggedMatrix NumericalTaggedQuery
  KP0SeedSpecialization.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Definition E_tagged_request_clause y p carrier marker root container theta z :=
  E_wal p (E_tagged_local_request y p carrier marker root container theta
    (E_raw_singleton y p z)).
Definition E_tagged_seed_kernel y input p carrier marker root container theta z :=
  E_wex container (E_wa
    (E_tagged_request_clause y p carrier marker root container theta z)
    (E_tagged_support y input carrier marker root container theta (E_raw_singleton y input z))).
Definition E_tagged_kernel y p carrier marker root container theta z :=
  E_wex container (E_wa
    (E_tagged_request_clause y p carrier marker root container theta z)
    (E_tagged_containment y carrier marker container theta)).

Definition tagged_kernel_parameters M input y carrier marker root theta z p k :=
  input .: y .: carrier .: marker .: root .: theta .: z .: p .: k .: fun _=>zeroM M.
Definition tagged_kernel_replacements :=
  (CEvar 0) .: (CEvar 1) .: (CEvar 8) .: (CEvar 7) .:
  (E_tagged_matrix (CEvar 1) (CEvar 0) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5) (CEvar 6)) .:
  (E_tagged_matrix (CEvar 1) (CEvar 7) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5) (CEvar 6)) .:
  (CEvar 4) .: fun _=>CEconst 0.

Lemma tagged_seed_kernel_expansion M input y carrier marker root theta z p k m query f :
  code_relation M (tagged_matrix_parameters M input y carrier marker root theta z)
    (E_tagged_matrix (CEvar 1) (CEvar 0) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5) (CEvar 6)) m ->
  code_relation M (tagged_query_parameters M input y carrier marker root theta z p)
    (E_tagged_matrix (CEvar 1) (CEvar 7) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5) (CEvar 6)) query ->
  code_relation M (kp0_seed_parameters M input y k p m query root)
    (E_kp_with_seed (CEvar 6) (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)) f ->
  code_relation M (tagged_kernel_parameters M input y carrier marker root theta z p k)
    (E_tagged_seed_kernel (CEvar 1) (CEvar 0) (CEvar 7) (CEvar 2) (CEvar 3)
      (CEvar 4) (CEvar 8) (CEvar 5) (CEvar 6)) f.
Proof.
  intros HM HQ HF.
  set (rho:=tagged_kernel_parameters M input y carrier marker root theta z p k).
  assert (HP:forall idx,code_relation M rho (tagged_kernel_replacements idx)
    (kp0_seed_parameters M input y k p m query root idx)).
  { intros [|[|[|[|[|[|[|idx]]]]]]];try reflexivity;assumption. }
  exact (proj2 (code_subst_graph M rho tagged_kernel_replacements
    (kp0_seed_parameters M input y k p m query root) HP
    (E_kp_with_seed (CEvar 6) (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)) f) HF).
Qed.

Lemma tagged_kernel_projection_program y input p carrier marker root container theta z :
  proof_macro nil
    (E_wim (E_tagged_support y input carrier marker root container theta (E_raw_singleton y input z))
      (E_tagged_containment y carrier marker container theta) :: nil)
    (E_wim (E_tagged_seed_kernel y input p carrier marker root container theta z)
      (E_tagged_kernel y p carrier marker root container theta z)).
Proof.
  unfold E_tagged_seed_kernel,E_tagged_kernel. apply macro_exists_monotone.
  apply macro_discharge,macro_deduction,kp0_md_conjunction.
  - apply tagged_md_left with
      (b:=E_tagged_support y input carrier marker root container theta (E_raw_singleton y input z)),
      md_hyp;now left.
  - eapply md_mp.
    + apply tagged_md_right with
        (a:=E_tagged_request_clause y p carrier marker root container theta z),md_hyp;now left.
    + apply md_global,PM_input;now left.
Qed.

Theorem numerical_tagged_kernel M input y carrier marker root theta z m :
  input<>zeroM M -> y<>input -> carrier<>input -> marker<>input -> root<>input ->
  y<>root -> z<>input -> z<>root ->
  formula_fresh M theta input -> named_binder_absent M theta root ->
  code_relation M (tagged_matrix_parameters M input y carrier marker root theta z)
    (E_tagged_matrix (CEvar 1) (CEvar 0) (CEvar 2) (CEvar 3)
      (CEvar 4) (CEvar 5) (CEvar 6)) m ->
  exists k p f,
    k<>input /\ k<>y /\ k<>root /\ input<>p /\ y<>p /\ k<>p /\ p<>root /\
    p<>zeroM M /\ formula_fresh M m k /\ formula_fresh M m p /\
    code_relation M (tagged_kernel_parameters M input y carrier marker root theta z p k)
      (E_tagged_kernel (CEvar 1) (CEvar 7) (CEvar 2) (CEvar 3)
        (CEvar 4) (CEvar 8) (CEvar 5) (CEvar 6)) f /\ numerically_provable M f.
Proof.
  intros H0 HYI HBI HTI HRI HYR HZI HZR HTheta HTR HM.
  destruct (numerical_tagged_query_instance M input y carrier marker root theta z m
    H0 HYI HBI HTI HRI HYR HZI HZR HTheta HTR HM)
    as (k & p & query & old & HKI & HKY & HKR & HIP & HYP & HKP & HPR & HP0 & HMK & HMP & HQ & HO & PO).
  set (rho:=tagged_kernel_parameters M input y carrier marker root theta z p k).
  set (Before:=E_tagged_seed_kernel (CEvar 1) (CEvar 0) (CEvar 7) (CEvar 2)
    (CEvar 3) (CEvar 4) (CEvar 8) (CEvar 5) (CEvar 6)).
  set (After:=E_tagged_kernel (CEvar 1) (CEvar 7) (CEvar 2)
    (CEvar 3) (CEvar 4) (CEvar 8) (CEvar 5) (CEvar 6)).
  assert (HBefore:code_relation M rho Before old).
  { exact (tagged_seed_kernel_expansion M input y carrier marker root theta z p k m query old HM HQ HO). }
  assert (PBefore:ns_proof M rho Before).
  { intros f HF. assert (E:f=old) by exact (code_relation_functional M Before rho f old HF HBefore).
    now subst f. }
  assert (PAfter:ns_proof M rho After).
  { apply (ns_proof_mp M rho Before After PBefore).
    apply (ns_proof_macro M rho
      (E_wim (E_tagged_support (CEvar 1) (CEvar 0) (CEvar 2) (CEvar 3) (CEvar 4)
        (CEvar 8) (CEvar 5) (E_raw_singleton (CEvar 1) (CEvar 0) (CEvar 6)))
        (E_tagged_containment (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 8) (CEvar 5)) :: nil)).
    - intros e [<-|[]]. apply (numerical_tagged_support_projection M rho
        (CEvar 1) (CEvar 0) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 8)
        (CEvar 5) (E_raw_singleton (CEvar 1) (CEvar 0) (CEvar 6)) input eq_refl H0).
      + intros v HV. change (v=y) in HV. now subst v.
      + intros v HV. change (v=carrier) in HV. now subst v.
      + intros v HV. change (v=marker) in HV. now subst v.
      + intros v HV. change (v=theta) in HV. now subst v.
    - apply tagged_kernel_projection_program. }
  destruct (code_relation_total M After rho) as [f HF].
  exists k,p,f. repeat split;try assumption. exact (PAfter f HF).
Qed.

Print Assumptions tagged_seed_kernel_expansion.
Print Assumptions numerical_tagged_kernel.
