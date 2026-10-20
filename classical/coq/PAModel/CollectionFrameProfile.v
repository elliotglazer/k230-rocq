(** The fixed Collection frame already forces its container to contain
    the empty marker.  Coverage and support then describe the very same
    container; no new witness or Collection premise is introduced. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates
  NamedLeibnizSteps NumericalKP0 NumericalKP0Eligibility ProofMacros QuantifierMacros
  NumericalSingleton NumericalRawPair NumericalTaggedComprehension RawMarkerExclusions RawMarkerQuantifiers
  CollectionKernel CollectionExceptionalRequests CollectionDistinguishedMembers
  CollectionCoverageNumerical CollectionFramePoint RawCollectionProfile.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Lemma collection_frame_marker_program T A B R C I W V Theta Z Q :
  proof_macro nil
    [E_wim (E_marker_empty T Z) (E_wim (E_raw_pair B T R Z) (E_wn (E_weq T R)));
     E_wim (E_marker_empty T Z) (E_collection_no_singletons W T Z);
     E_wim (E_collection_marker_exclusions T R W Z)
       (E_wim (E_marker_empty T Z)
         (E_wim (E_collection_requests T A B R C I W V Theta Z)
           (E_wim (E_wel B C) (E_wel T C))))]
    (E_wim (E_collection_frame T A B R C I W V Theta Z Q) (E_wel T C)).
Proof.
  set (fields:=collection_frame_fields T A B R C I W V Theta Z Q).
  set (inputs:=[E_wim (E_marker_empty T Z) (E_wim (E_raw_pair B T R Z) (E_wn (E_weq T R)));
     E_wim (E_marker_empty T Z) (E_collection_no_singletons W T Z);
     E_wim (E_collection_marker_exclusions T R W Z)
       (E_wim (E_marker_empty T Z)
         (E_wim (E_collection_requests T A B R C I W V Theta Z)
           (E_wim (E_wel B C) (E_wel T C))))]).
  apply macro_discharge,macro_deduction.
  assert (HFrame:macro_derivation nil inputs [E_collection_bundle fields] (E_collection_bundle fields)).
  { apply md_hyp;now left. }
  assert (HEmpty:macro_derivation nil inputs [E_collection_bundle fields] (E_marker_empty T Z)).
  { apply (collection_bundle_member nil inputs _ fields);[unfold fields,collection_frame_fields;cbn;tauto|exact HFrame]. }
  assert (HPair:macro_derivation nil inputs [E_collection_bundle fields] (E_raw_pair B T R Z)).
  { apply (collection_bundle_member nil inputs _ fields);[unfold fields,collection_frame_fields;cbn;tauto|exact HFrame]. }
  assert (HBC:macro_derivation nil inputs [E_collection_bundle fields] (E_wel B C)).
  { apply (collection_bundle_member nil inputs _ fields);[unfold fields,collection_frame_fields;cbn;tauto|exact HFrame]. }
  assert (HReq:macro_derivation nil inputs [E_collection_bundle fields] (E_collection_requests T A B R C I W V Theta Z)).
  { apply (collection_bundle_member nil inputs _ fields);[unfold fields,collection_frame_fields;cbn;tauto|exact HFrame]. }
  assert (HExcluded:macro_derivation nil inputs [E_collection_bundle fields] (E_collection_marker_exclusions T R W Z)).
  { unfold E_collection_marker_exclusions. apply kp0_md_conjunction.
    - eapply md_mp with (a:=E_raw_pair B T R Z);[exact HPair|].
      eapply md_mp with (a:=E_marker_empty T Z);[exact HEmpty|].
      apply md_global,PM_input;unfold inputs;now left.
    - eapply md_mp with (a:=E_marker_empty T Z);[exact HEmpty|].
      apply md_global,PM_input;unfold inputs;now right;left. }
  eapply md_mp with (a:=E_wel B C);[exact HBC|].
  eapply md_mp with (a:=E_collection_requests T A B R C I W V Theta Z);[exact HReq|].
  eapply md_mp with (a:=E_marker_empty T Z);[exact HEmpty|].
  eapply md_mp with (a:=E_collection_marker_exclusions T R W Z);[exact HExcluded|].
  apply md_global,PM_input;unfold inputs;now right;right;left.
Qed.

Theorem numerical_collection_frame_contains_marker M rho T A B R C I W V Theta Z Q
    t b r c i w v z :
  code_relation M rho T t -> code_relation M rho B b -> code_relation M rho R r ->
  code_relation M rho C c -> code_relation M rho I i -> code_relation M rho W w ->
  code_relation M rho V v -> code_relation M rho Z z ->
  NoDup [t;b;r;c;i;w;v;z] ->
  i<>zeroM M -> v<>zeroM M -> c<>zeroM M -> z<>zeroM M -> w<>zeroM M ->
  ns_proof M rho (E_wim (E_collection_frame T A B R C I W V Theta Z Q) (E_wel T C)).
Proof.
  intros HT HB HR HC HI HW HV HZ HND HI0 HV0 HC0 HZ0 HW0.
  pose proof (numerical_collection_marker_from_requests M rho T A B R C I W V Theta Z
    t b r c i w v z HT HB HR HC HI HW HV HZ HND HI0 HV0 HC0 HZ0) as HMarker.
  repeat match goal with H:NoDup (_::_) |- _ => inversion H;clear H end.
  repeat match goal with H:~ In _ (_::_) |- _ => apply not_in_cons in H;destruct H end.
  apply (ns_proof_macro M rho
    [E_wim (E_marker_empty T Z) (E_wim (E_raw_pair B T R Z) (E_wn (E_weq T R)));
     E_wim (E_marker_empty T Z) (E_collection_no_singletons W T Z);
     E_wim (E_collection_marker_exclusions T R W Z)
       (E_wim (E_marker_empty T Z)
         (E_wim (E_collection_requests T A B R C I W V Theta Z)
           (E_wim (E_wel B C) (E_wel T C))))]).
  - intros e [<-|[<-|[<-|[]]]].
    + apply (numerical_pair_not_empty_reverse M rho B T R Z b t z HB HT HZ HZ0);
        collection_discharge_name.
    + apply (numerical_empty_no_singletons M rho T W Z t w z HT HW HZ HZ0 HW0);
        collection_discharge_name.
    + exact HMarker.
  - apply collection_frame_marker_program.
Qed.

Lemma collection_frame_profile_program T A B R C I W V ThetaW Z Q X ThetaX :
  proof_macro nil
    [E_wim (E_collection_frame T A B R C I W V ThetaW Z Q) (E_wel T C);
     E_wim (E_collection_frame T A B R C I W V ThetaW Z Q)
       (E_wal X (E_raw_collection_coverage T A C X V ThetaX))]
    (E_wim
      (E_wa (E_collection_frame T A B R C I W V ThetaW Z Q)
        (E_wal V (E_raw_collection_support T A C X V ThetaX)))
      (E_raw_collection_profile T A C X V ThetaX)).
Proof.
  set (Frame:=E_collection_frame T A B R C I W V ThetaW Z Q).
  set (Cov:=E_wal X (E_raw_collection_coverage T A C X V ThetaX)).
  set (Sup:=E_wal V (E_raw_collection_support T A C X V ThetaX)).
  set (inputs:=[E_wim Frame (E_wel T C);E_wim Frame Cov]).
  apply macro_discharge,macro_deduction.
  assert (HF:macro_derivation nil inputs [E_wa Frame Sup] Frame).
  { apply tagged_md_left with (b:=Sup),md_hyp;now left. }
  unfold E_raw_collection_profile. apply kp0_md_conjunction.
  - eapply md_mp with (a:=Frame);[exact HF|].
    apply md_global,PM_input;unfold inputs;now left.
  - apply kp0_md_conjunction.
    + eapply md_mp with (a:=Frame);[exact HF|].
      apply md_global,PM_input;unfold inputs;now right;left.
    + apply tagged_md_right with (a:=Frame),md_hyp;now left.
Qed.

Theorem numerical_collection_frame_profile M rho T A B R C I W V ThetaW Z Q X ThetaX
    t b r c i w v z :
  code_relation M rho T t -> code_relation M rho B b -> code_relation M rho R r ->
  code_relation M rho C c -> code_relation M rho I i -> code_relation M rho W w ->
  code_relation M rho V v -> code_relation M rho Z z ->
  NoDup [t;b;r;c;i;w;v;z] ->
  i<>zeroM M -> v<>zeroM M -> c<>zeroM M -> z<>zeroM M -> w<>zeroM M ->
  ns_proof M rho (E_wim (E_collection_frame T A B R C I W V ThetaW Z Q)
    (E_wal X (E_raw_collection_coverage T A C X V ThetaX))) ->
  ns_proof M rho (E_wim
    (E_wa (E_collection_frame T A B R C I W V ThetaW Z Q)
      (E_wal V (E_raw_collection_support T A C X V ThetaX)))
    (E_raw_collection_profile T A C X V ThetaX)).
Proof.
  intros HT HB HR HC HI HW HV HZ HND HI0 HV0 HC0 HZ0 HW0 HCoverage.
  apply (ns_proof_macro M rho
    [E_wim (E_collection_frame T A B R C I W V ThetaW Z Q) (E_wel T C);
     E_wim (E_collection_frame T A B R C I W V ThetaW Z Q)
       (E_wal X (E_raw_collection_coverage T A C X V ThetaX))]).
  - intros e [<-|[<-|[]]].
    + exact (numerical_collection_frame_contains_marker M rho T A B R C I W V ThetaW Z Q
        t b r c i w v z HT HB HR HC HI HW HV HZ HND HI0 HV0 HC0 HZ0 HW0).
    + exact HCoverage.
  - apply collection_frame_profile_program.
Qed.

Print Assumptions numerical_collection_frame_contains_marker.
Print Assumptions numerical_collection_frame_profile.
