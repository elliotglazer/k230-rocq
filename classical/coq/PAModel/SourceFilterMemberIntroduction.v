(** Introduce membership in an actual Separation profile by specializing
    its universal binder. Every matrix is an arbitrary internal code. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SetSchemaConstructors SourceBounded NumericalContexts NumericalInstantiation
  NumericalSubstitutionMaps NumericalSubstitution SubstitutionSource SourceInstantiationConstructors
  NumericalSourceFull SourcePropositionalTemplates SourcePropositionalRebase
  SourceFilteredMinimumPrograms SourceCanonicalFilteredMinimum.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Theorem source_prop_expression_instantiation M env env' t a :
  (forall index,numerical_instantiation M (env index) t (env' index)) ->
  forall f g,code_relation M env (source_prop_expression a) f ->
    code_relation M env' (source_prop_expression a) g ->
    numerical_instantiation M f t g.
Proof.
  intro HI. induction a;intros f g HF HG;cbn [source_prop_expression] in HF,HG.
  - change (f=env n) in HF. change (g=env' n) in HG. subst f g. apply HI.
  - change (f=zeroM M) in HF. change (g=zeroM M) in HG. subst f g.
    destruct (substitution_singleton_total M t) as (b&c&HH&HT).
    exists b,c. split;[exact HH|].
    apply (proj2 (numerical_substitution_invalid M (zeroM M) b c
      (succM M (zeroM M)) (zeroM M) (zeroM M) (or_introl eq_refl))). reflexivity.
  - destruct (schema_expression_split M env SFImpl _ _ f HF) as (x&y&HX&HY&HF').
    destruct (schema_expression_split M env' SFImpl _ _ g HG) as (u&v&HU&HV&HG').
    exact (source_instantiation_binary M SFImpl x y f t u v g
      (or_intror (or_intror eq_refl)) HF' (IHa1 x u HX HU) (IHa2 y v HY HV) HG').
  - destruct (schema_expression_split M env SFAnd _ _ f HF) as (x&y&HX&HY&HF').
    destruct (schema_expression_split M env' SFAnd _ _ g HG) as (u&v&HU&HV&HG').
    exact (source_instantiation_binary M SFAnd x y f t u v g
      (or_introl eq_refl) HF' (IHa1 x u HX HU) (IHa2 y v HY HV) HG').
  - destruct (schema_expression_split M env SFOr _ _ f HF) as (x&y&HX&HY&HF').
    destruct (schema_expression_split M env' SFOr _ _ g HG) as (u&v&HU&HV&HG').
    exact (source_instantiation_binary M SFOr x y f t u v g
      (or_intror (or_introl eq_refl)) HF' (IHa1 x u HX HU) (IHa2 y v HY HV) HG').
Qed.

Theorem source_member_zero_successor_instantiation M s t member instance :
  sf_relation M SFMember (zeroM M) (succM M s) member ->
  sf_relation M SFMember t s instance ->numerical_instantiation M member t instance.
Proof.
  intros HM HI. destruct (substitution_singleton_total M t) as (b&c&HH&HT).
  exists b,c. split;[exact HH|].
  apply (proj2 (numerical_substitution_member M (zeroM M) (succM M s) member b c
    (succM M (zeroM M)) (zeroM M) instance HM)).
  exists t,s. split;[exact HH|]. split;[apply substitution_singleton_tail|exact HI].
Qed.

Theorem filtered_member_introduction_program :source_prop_program
  [filtered_minimum_profile;SPTSlot 1;SPTSlot 2] (SPTSlot 0).
Proof.
  eapply SPTIE.
  - eapply SPTCE2. apply SPTCtx. now left.
  - apply SPTCI;apply SPTCtx;cbn;tauto.
Qed.

Theorem source_full_filter_member_introduction M b c n k s a t phi instance
    allprofile memberS memberA :
  context_bounded M b c n k ->
  coding_lt M t k ->coding_lt M s k ->coding_lt M a k ->
  source_bounded M phi (succM M k) ->
  code_relation M (canonical_filter_environment phi s a) canonical_filter_profile allprofile ->
  numerical_instantiation M phi t instance ->
  sf_relation M SFMember t s memberS ->sf_relation M SFMember t a memberA ->
  source_full_prv M b c n allprofile ->source_full_prv M b c n memberA ->
  source_full_prv M b c n instance ->source_full_prv M b c n memberS.
Proof.
  intros HC HT HS HA HB HProfile HI HMemberS HMemberA PP PA PI.
  destruct (canonical_filter_profile_split M phi s a allprofile HProfile)
    as (point&smem&amem&HAll&HSmem&HAmem&HPoint).
  set (env:=schema_env3 memberS memberA instance).
  destruct (code_relation_total M (source_prop_expression filtered_minimum_profile) env)
    as (profile_instance&HProfileInstance).
  assert (HInst:numerical_instantiation M point t profile_instance).
  { apply (source_prop_expression_instantiation M (schema_env3 smem amem phi) env t
      filtered_minimum_profile);[|exact HPoint|exact HProfileInstance].
    intros [|[|index]];cbn [env schema_env3].
    - exact (source_member_zero_successor_instantiation M s t smem memberS HSmem HMemberS).
    - exact (source_member_zero_successor_instantiation M a t amem memberA HAmem HMemberA).
    - exact HI. }
  assert (PInstance:source_full_prv M b c n profile_instance).
  { apply (full_source_AllE M b c n point allprofile t profile_instance).
    - exact (source_wf_quantifier_instance M b c n SFAll point allprofile t profile_instance
        (or_introl eq_refl) HAll (source_full_prv_wellformed M b c n allprofile PP) HInst).
    - exact PP.
    - exact HAll.
    - exact HInst. }
  assert (HEnv:forall index,source_bounded M (env index) k).
  { intros [|[|index]];cbn [env schema_env3].
    - apply (proj2 (source_bounded_accept_atom M SFMember t s memberS k (or_introl eq_refl) HMemberS)). auto.
    - apply (proj2 (source_bounded_accept_atom M SFMember t a memberA k (or_introl eq_refl) HMemberA)). auto.
    - exact (numerical_instantiation_bounded M phi t instance k HB HT HI). }
  apply (source_prop_program_sound M _ _ filtered_member_introduction_program env k b c n memberS HEnv HC).
  - intros q [<-|[<-|[<-|[]]]] f HQ.
    + pose proof (code_relation_functional M _ env f profile_instance HQ HProfileInstance) as E.
      now subst f.
    + change (f=memberA) in HQ. now subst f.
    + change (f=instance) in HQ. now subst f.
  - reflexivity.
Qed.

Print Assumptions source_prop_expression_instantiation.
Print Assumptions source_member_zero_successor_instantiation.
Print Assumptions filtered_member_introduction_program.
Print Assumptions source_full_filter_member_introduction.
