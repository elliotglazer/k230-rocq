(** Derive Ord(m) and m subset A for filtered-set members from the actual
    ordinal-element law and the actual membership biconditional. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceBounded NumericalContexts NumericalSourceFull SourcePropositionalTemplates
  SourceSeparationPropositional SourceUniversalPrograms SourceFilteredMinimumPrograms.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Definition filtered_member_properties :=
  SPTImpl (SPTSlot 1) (SPTAnd (SPTSlot 3) (SPTSlot 4)).
Definition filtered_member_has_property i := SPTImpl (SPTSlot 0) (SPTSlot i).

Theorem filtered_member_ordinal_program : source_prop_program
  [filtered_minimum_profile;filtered_member_properties] (filtered_member_has_property 3).
Proof.
  unfold filtered_member_has_property. apply SPTII.
  eapply SPTCE1. eapply SPTIE.
  - apply SPTCtx. right;right;now left.
  - eapply SPTCE1. eapply SPTIE.
    + eapply SPTCE1. apply SPTCtx. right;now left.
    + apply SPTCtx. now left.
Qed.

Theorem filtered_member_subset_program : source_prop_program
  [filtered_minimum_profile;filtered_member_properties] (filtered_member_has_property 4).
Proof.
  unfold filtered_member_has_property. apply SPTII.
  eapply SPTCE2. eapply SPTIE.
  - apply SPTCtx. right;right;now left.
  - eapply SPTCE1. eapply SPTIE.
    + eapply SPTCE1. apply SPTCtx. right;now left.
    + apply SPTCtx. now left.
Qed.

Theorem source_full_filtered_member_property M rho k b c n i
    profile allprofile properties allproperties target alltarget :
  (i=3 \/ i=4) -> (forall j,source_bounded M (rho j) (succM M k)) ->
  context_bounded M b c n k ->
  code_relation M rho (source_prop_expression filtered_minimum_profile) profile ->
  code_relation M rho (source_prop_expression filtered_member_properties) properties ->
  code_relation M rho (source_prop_expression (filtered_member_has_property i)) target ->
  sf_relation M SFAll profile (zeroM M) allprofile ->
  sf_relation M SFAll properties (zeroM M) allproperties ->
  sf_relation M SFAll target (zeroM M) alltarget ->
  source_full_prv M b c n allprofile ->source_full_prv M b c n allproperties ->
  source_full_prv M b c n alltarget.
Proof.
  intros Choice HB HC HP HProp HT HAP HAProp HAT PP PProp.
  assert (Program:source_prop_program [filtered_minimum_profile;filtered_member_properties]
    (filtered_member_has_property i)).
  { destruct Choice as [ -> | -> ];[exact filtered_member_ordinal_program|exact filtered_member_subset_program]. }
  apply (source_full_universal_program M _ _ Program rho k b c n target alltarget HB HC);
    [|exact HT|exact HAT].
  intros q HQ f all HF HA. destruct HQ as [<-|[<-|[]]].
  - pose proof (code_relation_functional M _ rho f profile HF HP) as E. subst f.
    pose proof (sf_relation_functional M SFAll profile (zeroM M) all allprofile HA HAP) as E.
    now subst all.
  - pose proof (code_relation_functional M _ rho f properties HF HProp) as E. subst f.
    pose proof (sf_relation_functional M SFAll properties (zeroM M) all allproperties HA HAProp) as E.
    now subst all.
Qed.

Print Assumptions filtered_member_ordinal_program.
Print Assumptions filtered_member_subset_program.
Print Assumptions source_full_filtered_member_property.

