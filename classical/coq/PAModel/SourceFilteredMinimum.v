(** Genuine numerical source deductions for minima in a filtered set.
    Every predicate slot can be a nonstandard internally coded formula.
    The premises are ordinary source proofs of membership profiles,
    subset inclusion, and Foundation's disjointness conclusion. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceBounded NumericalContexts NumericalInstantiation SourceInstantiationConstructors
  NumericalSourceFull SourcePropositionalTemplates SourceSeparationPropositional
  SourceUniversalPrograms SourceFilteredMinimumPrograms.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Theorem source_full_filtered_minimum_exclusion M rho k b c n
    profile allprofile inclusion allinclusion exclusion allexclusion body allbody :
  (forall i, source_bounded M (rho i) (succM M k)) ->
  context_bounded M b c n k ->
  code_relation M rho (source_prop_expression filtered_minimum_profile) profile ->
  code_relation M rho (source_prop_expression filtered_minimum_inclusion) inclusion ->
  code_relation M rho (source_prop_expression filtered_minimum_exclusion) exclusion ->
  code_relation M rho (source_prop_expression filtered_predicate_exclusion) body ->
  sf_relation M SFAll profile (zeroM M) allprofile ->
  sf_relation M SFAll inclusion (zeroM M) allinclusion ->
  sf_relation M SFAll exclusion (zeroM M) allexclusion ->
  sf_relation M SFAll body (zeroM M) allbody ->
  source_full_prv M b c n allprofile -> source_full_prv M b c n allinclusion ->
  source_full_prv M b c n allexclusion -> source_full_prv M b c n allbody.
Proof.
  intros HB HC HP HI HE HD HAP HAI HAE HAD PP PI PE.
  apply (source_full_universal_program M _ _ filtered_minimum_exclusion_program
    rho k b c n body allbody HB HC);[|exact HD|exact HAD].
  intros q HQ point all HPoint HAll.
  destruct HQ as [<-|[<-|[<-|[]]]].
  - pose proof (code_relation_functional M _ rho point profile HPoint HP) as E. subst point.
    pose proof (sf_relation_functional M SFAll profile (zeroM M) all allprofile HAll HAP) as E.
    now subst all.
  - pose proof (code_relation_functional M _ rho point inclusion HPoint HI) as E. subst point.
    pose proof (sf_relation_functional M SFAll inclusion (zeroM M) all allinclusion HAll HAI) as E.
    now subst all.
  - pose proof (code_relation_functional M _ rho point exclusion HPoint HE) as E. subst point.
    pose proof (sf_relation_functional M SFAll exclusion (zeroM M) all allexclusion HAll HAE) as E.
    now subst all.
Qed.

Theorem source_full_filtered_member_predicate M rho k b c n profile :
  (forall i, source_bounded M (rho i) k) -> context_bounded M b c n k ->
  code_relation M rho (source_prop_expression filtered_minimum_profile) profile ->
  source_full_prv M b c n profile -> source_full_prv M b c n (rho 0) ->
  source_full_prv M b c n (rho 2).
Proof.
  intros HB HC HG HP HS.
  apply (source_prop_program_sound M _ _ filtered_minimum_predicate_program
    rho k b c n (rho 2) HB HC);[|reflexivity].
  intros q HQ f HF. destruct HQ as [<-|[<-|[]]].
  - pose proof (code_relation_functional M _ rho f profile HF HG) as E. now subst f.
  - change (f=rho 0) in HF. now subst f.
Qed.

Theorem source_full_filtered_member_container M rho k b c n profile :
  (forall i, source_bounded M (rho i) k) -> context_bounded M b c n k ->
  code_relation M rho (source_prop_expression filtered_minimum_profile) profile ->
  source_full_prv M b c n profile -> source_full_prv M b c n (rho 0) ->
  source_full_prv M b c n (rho 1).
Proof.
  intros HB HC HG HP HS.
  apply (source_prop_program_sound M _ _ filtered_minimum_container_program
    rho k b c n (rho 1) HB HC);[|reflexivity].
  intros q HQ f HF. destruct HQ as [<-|[<-|[]]].
  - pose proof (code_relation_functional M _ rho f profile HF HG) as E. now subst f.
  - change (f=rho 0) in HF. now subst f.
Qed.

Theorem source_full_filtered_member_specialization M rho k b c n matrix all t point :
  (forall i, source_bounded M (rho i) k) -> context_bounded M b c n k ->
  sf_relation M SFAll matrix (zeroM M) all -> numerical_instantiation M matrix t point ->
  code_relation M rho (source_prop_expression filtered_minimum_profile) point ->
  source_full_prv M b c n all -> source_full_prv M b c n (rho 0) ->
  source_full_prv M b c n (rho 1) /\ source_full_prv M b c n (rho 2).
Proof.
  intros HB HC HA HT HP PA PS.
  assert (PPoint:source_full_prv M b c n point).
  { apply (full_source_AllE M b c n matrix all t point).
    - exact (source_wf_quantifier_instance M b c n SFAll matrix all t point
        (or_introl eq_refl) HA (source_full_prv_wellformed M b c n all PA) HT).
    - exact PA.
    - exact HA.
    - exact HT. }
  split.
  - exact (source_full_filtered_member_container M rho k b c n point HB HC HP PPoint PS).
  - exact (source_full_filtered_member_predicate M rho k b c n point HB HC HP PPoint PS).
Qed.

Print Assumptions source_full_filtered_minimum_exclusion.
Print Assumptions source_full_filtered_member_predicate.
Print Assumptions source_full_filtered_member_container.
Print Assumptions source_full_filtered_member_specialization.
