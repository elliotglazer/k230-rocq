(** A single numerical K construction supplies all binary Collection
    requests and the raw support condition for the same container. *)
From PAModel Require Import Model FiniteCoding CodeExpressions CodeDescent
  NumericalProofs ProofTemplates FreshNames NamedSubstitution NamedSubstitutionFunctionality
  NamedBinderFresh TemplateFormulaFresh TemplateBinderFresh NumericalKP0Requests
  NumericalKP0Eligibility KP0SeedSpecialization CollectionSupportCleanup CollectionMatrixInstance.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Definition collection_query_parameters M i v t a b r u theta z p :=
  i .: v .: t .: a .: b .: r .: u .: theta .: z .: p .: fun _=>zeroM M.
Definition E_collection_parameter_query :=
  E_collection_choices (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)
    (CEvar 9) (CEvar 6) (CEvar 1) (CEvar 7) (CEvar 8).

Theorem numerical_collection_query_instance M i v t a b r u theta z m :
  i<>zeroM M -> v<>i -> t<>i -> a<>i -> b<>i -> r<>i -> u<>i -> z<>i ->
  i<>r -> v<>r -> u<>r -> z<>r ->
  formula_fresh M theta i -> named_binder_absent M theta r ->
  code_relation M (collection_matrix_parameters M i v t a b r u theta z)
    E_collection_parameter_matrix m ->
  exists k p query f,
    k<>i /\ k<>v /\ k<>r /\ i<>p /\ v<>p /\ k<>p /\ p<>r /\
    p<>zeroM M /\ formula_fresh M m k /\ formula_fresh M m p /\
    code_relation M (collection_query_parameters M i v t a b r u theta z p)
      E_collection_parameter_query query /\
    code_relation M (kp0_seed_parameters M i v k p m query r)
      (E_kp_with_seed (CEvar 6) (CEvar 0) (CEvar 1) (CEvar 2)
        (CEvar 3) (CEvar 4) (CEvar 5)) f /\ numerically_provable M f.
Proof.
  intros H0 HVI HTI HAI HBI HRI HUI HZI HIR HVR HUR HZR HTheta HTR HM.
  destruct (numerical_collection_matrix_instance M i v t a b r u theta z m
    H0 HVI HIR HVR HUI HUR HZI HZR (named_formula_fresh_binder_absent M theta i HTheta) HTR HM)
    as (k & p & mp & f & HKI & HKV & HKR & HIP & HVP & HKP & HPR & HP0 & HMK & HMP & HS & HF & PF).
  set (rho:=collection_query_parameters M i v t a b r u theta z p).
  assert (HA:code_relation M rho E_collection_parameter_matrix m) by exact HM.
  assert (HAF:expression_fresh M rho p E_collection_parameter_matrix).
  { intros w HW. assert (E:w=m) by exact (code_relation_functional M _ rho w m HW HA).
    now subst w. }
  destruct (collection_matrix_fresh_parts M rho p (CEvar 2) (CEvar 3) (CEvar 4)
    (CEvar 5) (CEvar 0) (CEvar 6) (CEvar 1) (CEvar 7) (CEvar 8) HAF)
    as (_ & _ & _ & _ & _ & HUP & HZP & HThetaP).
  destruct (code_relation_total M E_collection_parameter_query rho) as [query HQ].
  assert (HSub:named_substitution M m i p query).
  { apply (collection_matrix_input_substitution M rho (CEvar 2) (CEvar 3) (CEvar 4)
      (CEvar 5) (CEvar 0) (CEvar 9) (CEvar 6) (CEvar 1) (CEvar 7) (CEvar 8) i p u z
      eq_refl eq_refl eq_refl eq_refl H0 HUI (HUP u eq_refl) HZI (HZP z eq_refl)).
    - intros w HW. change (w=t) in HW. now subst w.
    - intros w HW. change (w=a) in HW. now subst w.
    - intros w HW. change (w=b) in HW. now subst w.
    - intros w HW. change (w=r) in HW. now subst w.
    - intros w HW. change (w=v) in HW. now subst w.
    - intros w HW. change (w=theta) in HW. now subst w.
    - intros w HW. exact (named_formula_fresh_binder_absent M w p (HThetaP w HW)).
    - exact HA.
    - exact HQ. }
  assert (E:mp=query) by exact (named_substitution_functional M m i p mp query HS HSub).
  subst mp. exists k,p,query,f. repeat split;assumption.
Qed.

Definition E_collection_requests T A B R C P U V Theta Z :=
  E_wal P (E_wim (E_kp_eligible R V C P)
    (E_kp_request V C (E_collection_choices T A B R P U V Theta Z))).
Definition E_collection_kernel T A B R C I P U V Theta Z :=
  E_wex C (E_wa (E_collection_requests T A B R C P U V Theta Z)
    (E_collection_raw_support T A B R C I U V Theta Z)).
Definition collection_kernel_parameters M i v t a b r u theta z p k :=
  i .: v .: t .: a .: b .: r .: u .: theta .: z .: p .: k .: fun _=>zeroM M.
Definition E_collection_parameter_kernel :=
  E_collection_kernel (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)
    (CEvar 10) (CEvar 0) (CEvar 9) (CEvar 6) (CEvar 1) (CEvar 7) (CEvar 8).
Definition collection_kernel_replacements :=
  (CEvar 0) .: (CEvar 1) .: (CEvar 10) .: (CEvar 9) .:
  E_collection_parameter_matrix .: E_collection_parameter_query .:
  (CEvar 5) .: fun _=>CEconst 0.

Lemma collection_kernel_expansion M i v t a b r u theta z p k m query f :
  code_relation M (collection_matrix_parameters M i v t a b r u theta z)
    E_collection_parameter_matrix m ->
  code_relation M (collection_query_parameters M i v t a b r u theta z p)
    E_collection_parameter_query query ->
  code_relation M (kp0_seed_parameters M i v k p m query r)
    (E_kp_with_seed (CEvar 6) (CEvar 0) (CEvar 1) (CEvar 2)
      (CEvar 3) (CEvar 4) (CEvar 5)) f ->
  code_relation M (collection_kernel_parameters M i v t a b r u theta z p k)
    E_collection_parameter_kernel f.
Proof.
  intros HM HQ HF.
  set (rho:=collection_kernel_parameters M i v t a b r u theta z p k).
  assert (HP:forall idx,code_relation M rho (collection_kernel_replacements idx)
    (kp0_seed_parameters M i v k p m query r idx)).
  { intros [|[|[|[|[|[|[|idx]]]]]]];try reflexivity;assumption. }
  exact (proj2 (code_subst_graph M rho collection_kernel_replacements
    (kp0_seed_parameters M i v k p m query r) HP
    (E_kp_with_seed (CEvar 6) (CEvar 0) (CEvar 1) (CEvar 2)
      (CEvar 3) (CEvar 4) (CEvar 5)) f) HF).
Qed.

Theorem numerical_collection_kernel M i v t a b r u theta z m :
  i<>zeroM M -> v<>i -> t<>i -> a<>i -> b<>i -> r<>i -> u<>i -> z<>i ->
  i<>r -> v<>r -> u<>r -> z<>r ->
  formula_fresh M theta i -> named_binder_absent M theta r ->
  code_relation M (collection_matrix_parameters M i v t a b r u theta z)
    E_collection_parameter_matrix m ->
  exists k p f,
    k<>i /\ k<>v /\ k<>r /\ i<>p /\ v<>p /\ k<>p /\ p<>r /\
    p<>zeroM M /\ formula_fresh M m k /\ formula_fresh M m p /\
    code_relation M (collection_kernel_parameters M i v t a b r u theta z p k)
      E_collection_parameter_kernel f /\ numerically_provable M f.
Proof.
  intros H0 HVI HTI HAI HBI HRI HUI HZI HIR HVR HUR HZR HTheta HTR HM.
  destruct (numerical_collection_query_instance M i v t a b r u theta z m
    H0 HVI HTI HAI HBI HRI HUI HZI HIR HVR HUR HZR HTheta HTR HM)
    as (k & p & query & f & HKI & HKV & HKR & HIP & HVP & HKP & HPR & HP0 & HMK & HMP & HQ & HF & PF).
  exists k,p,f. repeat split;try assumption.
  exact (collection_kernel_expansion M i v t a b r u theta z p k m query f HM HQ HF).
Qed.

Print Assumptions numerical_collection_query_instance.
Print Assumptions collection_kernel_expansion.
Print Assumptions numerical_collection_kernel.
