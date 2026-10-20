(** The matrix in the numerical KP0 request is exactly the intended
    tagged query, including an unchanged arbitrary internal predicate. *)
From PAModel Require Import Model FiniteCoding CodeExpressions CodeDescent
  NumericalProofs ProofTemplates FreshNames NamedSubstitution NamedSubstitutionFunctionality
  NamedBinderFresh TemplateFormulaFresh TemplateBinderFresh NumericalSingleton
  NumericalTaggedMatrix TaggedMatrixSubstitution KP0SeedSpecialization.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Definition tagged_query_parameters M input y carrier marker root theta z p :=
  input .: y .: carrier .: marker .: root .: theta .: z .: p .: fun _=>zeroM M.

Theorem numerical_tagged_query_instance M input y carrier marker root theta z m :
  input<>zeroM M -> y<>input -> carrier<>input -> marker<>input -> root<>input ->
  y<>root -> z<>input -> z<>root ->
  formula_fresh M theta input -> named_binder_absent M theta root ->
  code_relation M (tagged_matrix_parameters M input y carrier marker root theta z)
    (E_tagged_matrix (CEvar 1) (CEvar 0) (CEvar 2) (CEvar 3)
      (CEvar 4) (CEvar 5) (CEvar 6)) m ->
  exists k p query f,
    k<>input /\ k<>y /\ k<>root /\ input<>p /\ y<>p /\ k<>p /\ p<>root /\
    p<>zeroM M /\ formula_fresh M m k /\ formula_fresh M m p /\
    code_relation M (tagged_query_parameters M input y carrier marker root theta z p)
      (E_tagged_matrix (CEvar 1) (CEvar 7) (CEvar 2) (CEvar 3)
        (CEvar 4) (CEvar 5) (CEvar 6)) query /\
    code_relation M (kp0_seed_parameters M input y k p m query root)
      (E_kp_with_seed (CEvar 6) (CEvar 0) (CEvar 1) (CEvar 2)
        (CEvar 3) (CEvar 4) (CEvar 5)) f /\ numerically_provable M f.
Proof.
  intros H0 HYI HBI HTI HRI HYR HZI HZR HTheta HTR HM.
  destruct (numerical_tagged_matrix_instance M input y carrier marker root theta z m
    H0 HYI ltac:(congruence) HYR HZI HZR
    (named_formula_fresh_binder_absent M theta input HTheta) HTR HM)
    as (k & p & mp & f & HKI & HKY & HKR & HIP & HYP & HKP & HPR & HP0 & HMK & HMP & HS & HF & PF).
  set (rho:=tagged_query_parameters M input y carrier marker root theta z p).
  set (A:=E_tagged_matrix (CEvar 1) (CEvar 0) (CEvar 2) (CEvar 3)
      (CEvar 4) (CEvar 5) (CEvar 6)).
  set (B:=E_tagged_matrix (CEvar 1) (CEvar 7) (CEvar 2) (CEvar 3)
      (CEvar 4) (CEvar 5) (CEvar 6)).
  assert (HA:code_relation M rho A m) by exact HM.
  assert (HAF:expression_fresh M rho p A).
  { intros v HV. assert (E:v=m) by exact (code_relation_functional M A rho v m HV HA).
    now subst v. }
  destruct (tagged_matrix_fresh_parts M rho p (CEvar 1) (CEvar 0) (CEvar 2)
    (CEvar 3) (CEvar 4) (CEvar 5) (CEvar 6) HAF)
    as [_ [_ [_ [_ [_ [HZP HThetaP]]]]]].
  destruct (code_relation_total M B rho) as [query HQ].
  assert (HSub:named_substitution M m input p query).
  { apply (tagged_matrix_input_substitution M rho (CEvar 1) (CEvar 0) (CEvar 7)
      (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5) (CEvar 6) input p z
      eq_refl eq_refl eq_refl H0 HZI (HZP z eq_refl)).
    - intros v HV. change (v=y) in HV. now subst v.
    - intros v HV. change (v=carrier) in HV. now subst v.
    - intros v HV. change (v=marker) in HV. now subst v.
    - intros v HV. change (v=root) in HV. now subst v.
    - intros v HV. change (v=theta) in HV. now subst v.
    - intros v HV. exact (named_formula_fresh_binder_absent M v p (HThetaP v HV)).
    - exact HA.
    - exact HQ. }
  assert (E:mp=query) by exact (named_substitution_functional M m input p mp query HS HSub).
  subst mp. exists k,p,query,f. repeat split;assumption.
Qed.

Print Assumptions numerical_tagged_query_instance.
