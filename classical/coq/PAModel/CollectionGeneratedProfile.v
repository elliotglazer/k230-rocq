(** An actual generated K container satisfies the Collection profile under
    the finite envelope/pair context. All auxiliary request tags are chosen
    internally after K has produced its own fresh names. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  NumericalProofs ProofTemplates NamedLeibnizSteps TemplateFormulaFresh
  TemplateNamedSubstitution NumericalVacuitySteps FreshNames NamedBinderFresh NamedSubstitution
  CollectionSupportCleanup CollectionMatrixInstance CollectionKernel CollectionSupportedKernel
  CollectionProtectedInstance CollectionQueryTag CollectionFramePoint CollectionFrameFresh
  CollectionKernelProfile NumericalCollectionKernelProfile CollectionKernelExistence
  RawCollectionProfile RawMarkerQuantifiers NumericalSingleton NumericalKP0 NumericalKP0Requests
  NumericalKP0Eligibility CollectionFreshAllocation CollectionMatrixFreshNames.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Definition collection_generated_parameters M t a b r k x v z q theta :=
  t .: a .: b .: r .: k .: x .: v .: z .: q .: theta .: fun _=>zeroM M.
Definition E_collection_generated_statement :=
  E_wim (E_collection_outer (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 7) (CEvar 8))
    (E_wex (CEvar 4) (E_raw_collection_profile (CEvar 0) (CEvar 1) (CEvar 4)
      (CEvar 5) (CEvar 6) (CEvar 9))).

Theorem numerical_collection_generated_profile M t a b r j x w v z q target thetaX thetaW :
  NoDup (t::a::b::r::j::x::w::v::z::q::target::nil) ->
  j<>zeroM M -> x<>zeroM M -> w<>zeroM M -> v<>zeroM M -> z<>zeroM M -> q<>zeroM M ->
  formula_fresh M thetaW j -> named_binder_absent M thetaW r ->
  formula_fresh M thetaX w -> formula_fresh M thetaX j -> named_binder_absent M thetaX r ->
  named_substitution M thetaX x w thetaW ->
  exists k f,k<>zeroM M /\ k<>target /\ t<>k /\ a<>k /\ x<>k /\ v<>k /\ formula_fresh M thetaX k /\
    code_relation M (collection_generated_parameters M t a b r k x v z q thetaX)
      E_collection_generated_statement f /\ numerically_provable M f.
Proof.
  intros HND HJ0 HX0 HW0 HV0 HZ0 HQ0 HTJ HTR HXW HXJ HXR HSub.
  assert (Hrestore:True->NoDup (t::a::b::r::j::x::w::v::z::q::target::nil)) by (intros _;exact HND).
  repeat match goal with H:NoDup (_::_) |- _ => inversion H;clear H end.
  repeat match goal with H:~ In _ (_::_) |- _ => apply not_in_cons in H;destruct H end.
  set (r0:=collection_matrix_parameters M j v t a b r w thetaW z).
  destruct (code_relation_total M E_collection_parameter_matrix r0) as [m HM].
  destruct (numerical_collection_protected_kernel M j v t a b r w thetaW z x q target m thetaX
    HJ0 ltac:(congruence) ltac:(congruence) ltac:(congruence) ltac:(congruence)
    ltac:(congruence) ltac:(congruence) ltac:(congruence) ltac:(congruence)
    ltac:(congruence) ltac:(congruence) ltac:(congruence) ltac:(congruence)
    ltac:(congruence) ltac:(congruence) HTJ HTR HXJ HXR HM)
    as (k&query&kf&HKJ&HKV&HKR&HJP&HVP&HKP&HPR&HP0&HKX&HKQ&HKT&HPX&HPQ&HPT&FMK&FMP&FXK&FXP&HK&PK).
  assert (EFK:expression_fresh M r0 k E_collection_parameter_matrix).
  { intros f Hf. rewrite (code_relation_functional M _ r0 f m Hf HM). exact FMK. }
  assert (EFP:expression_fresh M r0 query E_collection_parameter_matrix).
  { intros f Hf. rewrite (code_relation_functional M _ r0 f m Hf HM). exact FMP. }
  destruct (collection_matrix_fresh_parts M r0 k (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)
    (CEvar 0) (CEvar 6) (CEvar 1) (CEvar 7) (CEvar 8) EFK)
    as (_&RK&VK&BK&TK&WK&ZK&ThetaK).
  destruct (collection_matrix_fresh_parts M r0 query (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)
    (CEvar 0) (CEvar 6) (CEvar 1) (CEvar 7) (CEvar 8) EFP)
    as (_&RP&VP&BP&TP&WP&ZP&ThetaP).
  assert (HK0:k<>zeroM M) by exact (collection_matrix_fresh_nonzero M r0 k
    (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5) (CEvar 0) (CEvar 6) (CEvar 1) (CEvar 7) (CEvar 8) EFK).
  destruct (collection_query_tag_allocation M thetaX thetaW
    (zeroM M::t::a::b::r::k::query::j::x::w::v::z::q::target::nil))
    as (base&tag&HTag&HB0&HBound&HNotTag&FTagX&FTagW).
  assert (HTag0:tag<>zeroM M) by (intro E;apply (HNotTag (zeroM M));[now left|symmetry;exact E]).
  assert (no_tag:forall y,In y (t::a::b::r::k::query::j::x::w::v::z::q::target::nil) -> y<>tag).
  { intros y Hy. apply HNotTag;now right. }
  set (rho:=t .: a .: b .: r .: k .: query .: j .: x .: tag .: w .: v .: z .: q .: base .: thetaX .: thetaW .: fun _=>zeroM M).
  assert (HFrame:expression_fresh M rho tag
    (E_collection_frame (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)
      (CEvar 9) (CEvar 10) (CEvar 15) (CEvar 11) (CEvar 12))).
  { apply collection_frame_expression_fresh;[exact HTag0| | | | | | | | | | |].
    all:try (intros y Hy;cbn in Hy;subst y;apply no_tag;cbn;tauto).
    intros f Hf. change (f=thetaW) in Hf. now subst f. }
  assert (HGoal:expression_fresh M rho tag
    (E_raw_collection_coverage (CEvar 0) (CEvar 1) (CEvar 4) (CEvar 7) (CEvar 10) (CEvar 14))).
  { assert (HT:expression_name_avoids M rho tag (CEvar 0)) by (intros y Hy;change (y=t) in Hy;subst y;apply no_tag;cbn;tauto).
    assert (HA:expression_name_avoids M rho tag (CEvar 1)) by (intros y Hy;change (y=a) in Hy;subst y;apply no_tag;cbn;tauto).
    assert (HC:expression_name_avoids M rho tag (CEvar 4)) by (intros y Hy;change (y=k) in Hy;subst y;apply no_tag;cbn;tauto).
    assert (HX:expression_name_avoids M rho tag (CEvar 7)) by (intros y Hy;change (y=x) in Hy;subst y;apply no_tag;cbn;tauto).
    assert (HV:expression_name_avoids M rho tag (CEvar 10)) by (intros y Hy;change (y=v) in Hy;subst y;apply no_tag;cbn;tauto).
    assert (HF:expression_fresh M rho tag (CEvar 14)) by (intros f Hf;change (f=thetaX) in Hf;now subst f).
    unfold E_raw_collection_coverage. collection_frame_fresh. }
  assert (HND:NoDup (t::a::b::r::k::query::x::tag::w::v::z::q::nil)).
  { apply (collection_allocated_roles_nodup M j v t a b r w thetaW z m x q target k query tag
      (Hrestore I) HM FMK FMP HKP HKX HKQ HPX HPQ).
    intros y Hy. apply coding_lt_trans with (y:=base).
    - apply HBound. clear - Hy. cbn in Hy|-*. tauto.
    - rewrite HTag. apply coding_lt_trans with (y:=succM M base);apply coding_lt_succ. }
  assert (HXBase:coding_lt M x base) by (apply HBound;cbn;tauto).
  assert (HZBase:coding_lt M z base) by (apply HBound;cbn;tauto).
  assert (EQuery:expression_fresh M rho query (CEvar 15)).
  { intros f Hf. change (f=thetaW) in Hf. subst f. exact (ThetaP thetaW eq_refl). }
  assert (EW:expression_fresh M rho w (CEvar 14)).
  { intros f Hf. change (f=thetaX) in Hf. now subst f. }
  assert (ETag:expression_fresh M rho tag (CEvar 15)).
  { intros f Hf. change (f=thetaW) in Hf. now subst f. }
  assert (EJ:expression_fresh M rho j (CEvar 15)).
  { intros f Hf. change (f=thetaW) in Hf. now subst f. }
  assert (ESub:expression_named_substitution M rho rho x w (CEvar 14) (CEvar 15)).
  { intros f g Hf Hg. change (f=thetaX) in Hf. change (g=thetaW) in Hg. now subst f g. }
  assert (HLocal:ns_proof M rho
    (E_wim (E_collection_outer (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 11) (CEvar 12))
      (E_wim (E_wa (E_collection_requests (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4)
        (CEvar 5) (CEvar 9) (CEvar 10) (CEvar 15) (CEvar 11))
        (E_collection_raw_support (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4)
          (CEvar 6) (CEvar 9) (CEvar 10) (CEvar 15) (CEvar 11)))
        (E_raw_collection_profile (CEvar 0) (CEvar 1) (CEvar 4) (CEvar 7) (CEvar 10) (CEvar 14))))).
  { apply (numerical_collection_kernel_profile M rho
      (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5) (CEvar 6) (CEvar 7)
      (CEvar 8) (CEvar 9) (CEvar 10) (CEvar 11) (CEvar 12) (CEvar 13) (CEvar 14) (CEvar 15)
      t a b r k query j x tag w v z q base).
    all:try reflexivity;try assumption;try congruence. }
  assert (HKernel:ns_proof M rho (E_collection_kernel
      (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4)
      (CEvar 6) (CEvar 5) (CEvar 9) (CEvar 10) (CEvar 15) (CEvar 11))).
  { intros f Hf.
    assert (HGraph:code_relation M rho (E_collection_kernel
      (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4)
      (CEvar 6) (CEvar 5) (CEvar 9) (CEvar 10) (CEvar 15) (CEvar 11)) kf) by exact HK.
    rewrite (code_relation_functional M _ rho f kf Hf HGraph). exact PK. }
  assert (HOuter:expression_fresh M rho k (E_collection_outer
      (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 11) (CEvar 12))).
  { destruct (collection_matrix_fresh_numeric_names M j v t a b r w thetaW z m k HM FMK)
      as [_ HKN].
    apply collection_outer_fresh;[exact HK0| | | | | |].
    all:intros y Hy;cbn in Hy;subst y.
    all:try (apply HKN;cbn;tauto).
    intro E. apply HKQ. symmetry;exact E. }
  assert (PFinal:ns_proof M rho
      (E_wim (E_collection_outer (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 11) (CEvar 12))
        (E_wex (CEvar 4) (E_raw_collection_profile (CEvar 0) (CEvar 1) (CEvar 4)
          (CEvar 7) (CEvar 10) (CEvar 14))))).
  { eapply numerical_collection_container_map.
    - exact HLocal.
    - apply (kp0_expression_fresh_vacuity M rho (CEvar 4) _ k eq_refl HOuter).
    - exact HKernel. }
  destruct (code_relation_total M E_collection_generated_statement
    (collection_generated_parameters M t a b r k x v z q thetaX)) as [f Hf].
  destruct (collection_matrix_fresh_numeric_names M j v t a b r w thetaW z m k HM FMK)
    as [_ HKN].
  assert (HTK:t<>k) by (apply HKN;now left).
  assert (HAK:a<>k) by (apply HKN;now right;left).
  assert (HXK:x<>k) by congruence.
  assert (HVK:v<>k) by (apply HKN;do 6 right;now left).
  exists k,f. repeat split;try assumption. exact (PFinal f Hf).
Qed.

Print Assumptions numerical_collection_generated_profile.





