(** Assemble coverage and support at the one container supplied by K.
    The envelope and pair remain explicit object hypotheses here. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  ProofTemplates ProofMacros QuantifierMacros NamedLeibnizSteps NumericalKP0 NumericalKP0Requests
  NumericalKP0Eligibility NumericalBootstrap NumericalSingleton NumericalRawPair NumericalRawEnvelope
  NumericalTaggedComprehension RawMarkerExclusions RawMarkerQuantifiers
  TemplateFormulaFresh TemplateNamedSubstitution NumericalVacuitySteps RawCollectionProfile
  CollectionSupportCleanup CollectionKernel CollectionFramePoint CollectionFrameConclusion
  CollectionDistinguishedMembers CollectionCoverageNumerical CollectionExceptionalRequests.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Definition collection_outer_fields T A B R Z Q :=
 [E_marker_empty T Z;E_wn (E_weq B T);E_raw_pair B T R Z;
  E_raw_envelope T A B Q;E_wn (E_wel T B)].
Definition E_collection_outer T A B R Z Q := E_collection_bundle (collection_outer_fields T A B R Z Q).

Lemma collection_bundle_construct G inputs delta xs :
  (forall f,In f xs -> macro_derivation G inputs delta f) ->
  macro_derivation G inputs delta (E_collection_bundle xs).
Proof.
  induction xs as [|a rest IH];intro H;cbn.
  - apply md_global,PM_template. apply TP_true.
  - apply kp0_md_conjunction.
    + apply H;now left.
    + apply IH. intros f Hf. apply H;now right.
Qed.

Lemma collection_outer_profile_program T A B R C I J W V ThetaW Z Q X ThetaX :
  proof_macro nil
   [E_wim (E_marker_empty T Z) (E_wim (E_raw_pair B T R Z) (E_wn (E_weq R T)));
    E_wim (E_wn (E_weq B T)) (E_wim (E_raw_pair B T R Z) (E_collection_no_singletons W R Z));
    E_wim (E_collection_root_exclusions T R W Z)
      (E_wim (E_collection_requests T A B R C I W V ThetaW Z) (E_wel B C));
    E_wim (E_marker_empty T Z) (E_wim (E_wn (E_wel T B))
      (E_wim (E_collection_raw_support T A B R C J W V ThetaW Z)
        (E_wal V (E_raw_collection_support T A C W V ThetaW))));
    E_wim (E_wa (E_collection_frame T A B R C I W V ThetaW Z Q)
        (E_wal V (E_raw_collection_support T A C W V ThetaW)))
      (E_raw_collection_profile T A C X V ThetaX)]
   (E_wim (E_collection_outer T A B R Z Q)
     (E_wim (E_wa (E_collection_requests T A B R C I W V ThetaW Z)
        (E_collection_raw_support T A B R C J W V ThetaW Z))
       (E_raw_collection_profile T A C X V ThetaX))).
Proof.
  set (Outer:=E_collection_outer T A B R Z Q).
  set (Req:=E_collection_requests T A B R C I W V ThetaW Z).
  set (Raw:=E_collection_raw_support T A B R C J W V ThetaW Z).
  set (Frame:=E_collection_frame T A B R C I W V ThetaW Z Q).
  set (Sup:=E_wal V (E_raw_collection_support T A C W V ThetaW)).
  set (Profile:=E_raw_collection_profile T A C X V ThetaX).
  set (inputs:=[E_wim (E_marker_empty T Z) (E_wim (E_raw_pair B T R Z) (E_wn (E_weq R T)));
    E_wim (E_wn (E_weq B T)) (E_wim (E_raw_pair B T R Z) (E_collection_no_singletons W R Z));
    E_wim (E_collection_root_exclusions T R W Z) (E_wim Req (E_wel B C));
    E_wim (E_marker_empty T Z) (E_wim (E_wn (E_wel T B)) (E_wim Raw Sup));
    E_wim (E_wa Frame Sup) Profile]).
  apply macro_discharge. do 2 apply macro_deduction.
  set (ctx:=[E_wa Req Raw;Outer]).
  assert (HO:macro_derivation nil inputs ctx Outer) by (apply md_hyp;now right;left).
  assert (outer:forall f,In f (collection_outer_fields T A B R Z Q) -> macro_derivation nil inputs ctx f).
  { intros f Hf. apply (collection_bundle_member nil inputs ctx (collection_outer_fields T A B R Z Q));assumption. }
  assert (HE:macro_derivation nil inputs ctx (E_marker_empty T Z)).
  { apply outer;unfold collection_outer_fields;cbn;tauto. }
  assert (HN:macro_derivation nil inputs ctx (E_wn (E_weq B T))).
  { apply outer;unfold collection_outer_fields;cbn;tauto. }
  assert (HPair:macro_derivation nil inputs ctx (E_raw_pair B T R Z)).
  { apply outer;unfold collection_outer_fields;cbn;tauto. }
  assert (HReq:macro_derivation nil inputs ctx Req) by (apply tagged_md_left with (b:=Raw),md_hyp;now left).
  assert (HEx:macro_derivation nil inputs ctx (E_collection_root_exclusions T R W Z)).
  { unfold E_collection_root_exclusions. apply kp0_md_conjunction;
      eapply md_mp;[exact HPair|eapply md_mp;[exact HE|apply md_global,PM_input;unfold inputs;now left]|
      exact HPair|eapply md_mp;[exact HN|apply md_global,PM_input;unfold inputs;now right;left]]. }
  assert (HBC:macro_derivation nil inputs ctx (E_wel B C)).
  { eapply md_mp;[exact HReq|]. eapply md_mp;[exact HEx|].
    apply md_global,PM_input;unfold inputs;now right;right;left. }
  assert (HF:macro_derivation nil inputs ctx Frame).
  { unfold Frame,E_collection_frame. apply collection_bundle_construct.
    intros f Hf. unfold collection_frame_fields in Hf. cbn in Hf.
    destruct Hf as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
    - exact HE.
    - exact HN.
    - exact HPair.
    - apply outer;unfold collection_outer_fields;cbn;tauto.
    - exact HBC.
    - exact HReq. }
  assert (HS:macro_derivation nil inputs ctx Sup).
  { eapply md_mp with (a:=Raw).
    - apply tagged_md_right with (a:=Req),md_hyp;now left.
    - eapply md_mp with (a:=E_wn (E_wel T B)).
      + apply outer;unfold collection_outer_fields;cbn;tauto.
      + eapply md_mp;[exact HE|]. apply md_global,PM_input;unfold inputs;now right;right;right;left. }
  eapply md_mp with (a:=E_wa Frame Sup);[now apply kp0_md_conjunction|].
  apply md_global,PM_input;unfold inputs;now right;right;right;right;left.
Qed.

Print Assumptions collection_outer_profile_program.



