(** The genuine Collection kernel keeps generated names disjoint from three
    additional external roles, without changing the eventual unpadded matrix. *)
From PAModel Require Import Model FiniteCoding CodeExpressions CodeDescent
  NumericalProofs ProofTemplates FreshNames NamedBinderFresh NamedSubstitution
  NamedSubstitutionFunctionality TemplateFormulaFresh CollectionSupportCleanup
  CollectionMatrixInstance CollectionKernel CollectionProtectedKernel.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Theorem numerical_collection_protected_kernel M i v t a b r u theta z x q d m original :
  i<>zeroM M -> v<>i -> t<>i -> a<>i -> b<>i -> r<>i -> u<>i -> z<>i ->
  i<>r -> v<>r -> u<>r -> z<>r -> x<>i -> q<>i -> d<>i ->
  formula_fresh M theta i -> named_binder_absent M theta r ->
  formula_fresh M original i -> named_binder_absent M original r ->
  code_relation M (collection_matrix_parameters M i v t a b r u theta z)
    E_collection_parameter_matrix m ->
  exists k p f,
    k<>i /\ k<>v /\ k<>r /\ i<>p /\ v<>p /\ k<>p /\ p<>r /\ p<>zeroM M /\
    k<>x /\ k<>q /\ k<>d /\ p<>x /\ p<>q /\ p<>d /\
    formula_fresh M m k /\ formula_fresh M m p /\
    formula_fresh M original k /\ formula_fresh M original p /\
    code_relation M (collection_kernel_parameters M i v t a b r u theta z p k)
      E_collection_parameter_kernel f /\ numerically_provable M f.
Proof.
  intros H0 HVI HTI HAI HBI HRI HUI HZI HIR HVR HUR HZR HXI HQI HDI HTheta HTR HOrigI HOrigR HM.
  set (r0:=collection_matrix_parameters M i v t a b r u theta z).
  assert (HMI:named_binder_absent M m i).
  { exact (collection_matrix_binder_absent M r0 i (CEvar 2) (CEvar 3) (CEvar 4)
      (CEvar 5) (CEvar 0) (CEvar 6) (CEvar 1) (CEvar 7) (CEvar 8) u z
      eq_refl eq_refl HUI HZI
      ltac:(intros f Hf;change (f=theta) in Hf;subst f;exact (named_formula_fresh_binder_absent M theta i HTheta)) m HM). }
  assert (HMR:named_binder_absent M m r).
  { exact (collection_matrix_binder_absent M r0 r (CEvar 2) (CEvar 3) (CEvar 4)
      (CEvar 5) (CEvar 0) (CEvar 6) (CEvar 1) (CEvar 7) (CEvar 8) u z
      eq_refl eq_refl HUR HZR ltac:(intros f Hf;change (f=theta) in Hf;now subst f) m HM). }
  assert (Hmention:formula_mentions M m r).
  { exact (collection_matrix_mentions_root M r0 (CEvar 2) (CEvar 3) (CEvar 4)
      (CEvar 5) (CEvar 0) (CEvar 6) (CEvar 1) (CEvar 7) (CEvar 8) r eq_refl m HM). }
  destruct (numerical_collection_protected_kp0 M i v r x q d m original H0 HVI HIR HVR HXI HQI HDI HMI HMR Hmention HOrigI HOrigR)
    as (k&p&mp&f&HKI&HKV&HKR&HIP&HVP&HKP&HPR&HP0&HKX&HKQ&HKD&HPX&HPQ&HPD&HMK&HMP&HOK&HOP&HS&HF&PF).
  set (rho:=collection_query_parameters M i v t a b r u theta z p).
  assert (HA:code_relation M rho E_collection_parameter_matrix m) by exact HM.
  assert (HAF:expression_fresh M rho p E_collection_parameter_matrix).
  { intros w HW. rewrite (code_relation_functional M _ rho w m HW HA). exact HMP. }
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
  subst mp. exists k,p,f. repeat split;try assumption.
  exact (collection_kernel_expansion M i v t a b r u theta z p k m query f HM HQ HF).
Qed.

Print Assumptions numerical_collection_protected_kernel.
