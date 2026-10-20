(** Actual raw Collection certificates in every PA model. The K kernel,
    singleton queries, outer witnesses, and binder normalization are all
    proved components; no raw Collection certificate is assumed. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
  NumericalProofs ProofTemplates TemplatePropositional NamedLeibnizSteps NamedAlpha
  NumericalEquivalence NumericalVacuitySteps NumericalKP0Eligibility TemplateFormulaFresh TemplateBinderFresh TemplateNamedSubstitution
  NamedBinderFresh NamedSubstitution FreshNames RawMarkerExclusions RawQuotientAtomCongruence
  NumericalRawEnvelope NumericalRawPair EmptyRebind RawCollectionProfile
  CollectionGeneratedProfile CollectionKernelProfile CollectionEnvelopeAssembly
  CollectionOuterAllocation CollectionAuxiliaryClosure CollectionDistinctInputContract
  RawCollectionContainerNormalize.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Theorem actual_distinct_input_raw_collection M t z0 marker :
  raw_empty_marker_graph M t z0 marker ->
  distinct_input_raw_collection_certificates M t marker.
Proof.
  intros [HZ00 [HTZ0 HM]] a c x v theta HAT HC0 HX0 HV0 HTC HTX HTV HAC HAX HAV HCX HCV HXV HF HAbsX HAbsV out HOut.
  assert (ND:NoDup (t::a::c::x::v::nil)).
  { repeat constructor;cbn;intuition congruence. }
  destruct (collection_outer_allocation_total M t a c x v theta ND HAbsX HAbsV) as [alloc].
  destruct alloc as [w thetaW j z q b r baseB baseR final step HND HW0 HJ0 HZ0 HQ0 HSub
    HTWJ HTWR HTW HTJ HTR EB ER BB BR HG HS HGB HSR].
  destruct (numerical_collection_generated_profile M t a b r j x w v z q c theta thetaW
    HND HJ0 HX0 HW0 HV0 HZ0 HQ0 HTWJ HTWR HTW HTJ HTR HSub)
    as (k & gen & HK0 & HKC & HTK & HAK & HXK & HVK & HThetaK & HGen & PGen).
  set (rho:=t .: a .: c .: x .: v .: theta .: z .: q .: b .: r .: baseB .: baseR .: k .: z0 .: fun _=>zeroM M).
  set (Goal:=E_collection_closure_goal).
  set (Outer:=E_collection_outer (CEvar 0) (CEvar 1) (CEvar 8) (CEvar 9) (CEvar 6) (CEvar 7)).
  set (KGoal:=E_wex (CEvar 12) (E_raw_collection_profile (CEvar 0) (CEvar 1) (CEvar 12)
    (CEvar 3) (CEvar 4) (CEvar 5))).
  assert (PGenerated:ns_proof M rho (E_wim Outer KGoal)).
  { intros f Hf.
    assert (HG':code_relation M rho (E_wim Outer KGoal) gen) by exact HGen.
    rewrite (code_relation_functional M _ rho f gen Hf HG'). exact PGen. }
  assert (PNorm:ns_proof M rho (E_wim KGoal Goal)).
  { apply (numerical_raw_collection_exists_normalize M rho (CEvar 0) (CEvar 1) (CEvar 12)
      (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5) t a k c x v).
    all:try reflexivity;try assumption;try congruence.
    - intros f Hf. change (f=theta) in Hf. now subst f.
    - intros f Hf. change (f=theta) in Hf. now subst f. }
  assert (POuter:ns_proof M rho (E_wim Outer Goal)).
  { eapply ns_proof_syl;[exact PGenerated|exact PNorm]. }
  assert (Hrestore:True->NoDup (t::a::b::r::j::x::w::v::z::q::c::nil)) by (intros _;exact HND).
  repeat match goal with H:NoDup (_::_) |- _ => inversion H;clear H end.
  repeat match goal with H:~ In _ (_::_) |- _ => apply not_in_cons in H;destruct H end.
  assert (PConstruction:ns_proof M rho
    (E_wim (E_marker_empty (CEvar 0) (CEvar 6)) (E_wim (E_wel (CEvar 0) (CEvar 1))
      (E_wim (E_raw_envelope (CEvar 0) (CEvar 1) (CEvar 8) (CEvar 7))
        (E_wim (E_raw_pair (CEvar 8) (CEvar 0) (CEvar 9) (CEvar 6)) Goal))))).
  { apply (numerical_collection_outer_from_envelope M rho (CEvar 0) (CEvar 1) (CEvar 8) (CEvar 9)
      (CEvar 6) (CEvar 7) Goal t a b z q);try reflexivity;try assumption;congruence. }
  assert (FreshB:expression_fresh M rho b E_collection_closure_final).
  { intros f Hf. assert (HG':code_relation M rho E_collection_closure_final final) by exact HG.
    rewrite (code_relation_functional M _ rho f final Hf HG'). exact HGB. }
  assert (FreshR:expression_fresh M rho r E_collection_closure_step).
  { intros f Hf. assert (HS':code_relation M rho E_collection_closure_step step) by exact HS.
    rewrite (code_relation_functional M _ rho f step Hf HS'). exact HSR. }
  assert (PFinal:ns_proof M rho E_collection_closure_final).
  { apply (numerical_collection_close_auxiliaries M rho (CEvar 0) (CEvar 1) (CEvar 8) (CEvar 9)
      (CEvar 6) (CEvar 7) (CEvar 10) (CEvar 11) Goal t a b r z q baseB baseR).
    all:try reflexivity;try assumption;try congruence.
    all:first [apply BB;cbn;tauto|apply BR;cbn;tauto]. }
  set (OldEmp:=E_marker_empty (CEvar 0) (CEvar 13)).
  set (Target:=E_raw_collection_statement (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)).
  assert (POld:ns_proof M rho (E_wim OldEmp Target)).
  { destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
      (fun ax H env=>axioms M ax env H) z0 z) as [E|HNe].
    - subst z0. exact PFinal.
    - eapply ns_proof_syl;[|exact PFinal].
      apply (numerical_empty_rebind M rho (CEvar 0) (CEvar 13) (CEvar 6) t z0 z);
        try reflexivity;try assumption;try congruence.
      + exact (template_lt_different M _ _ HZ00).
      + exact (not_eq_sym (template_lt_different M _ _ HTZ0)). }
  assert (HOldGraph:code_relation M rho OldEmp marker) by exact HM.
  assert (HTargetGraph:code_relation M rho Target out) by exact HOut.
  exact (proj1 (numerical_implies_expression M rho OldEmp Target marker out HOldGraph HTargetGraph) POld).
Qed.

Theorem actual_raw_collection_template_certificates M t z marker :
  raw_empty_marker_graph M t z marker -> raw_collection_template_certificates M t marker.
Proof.
  intro HM. apply (raw_collection_certificates_from_distinct_input M t z marker HM).
  exact (actual_distinct_input_raw_collection M t z marker HM).
Qed.

Print Assumptions actual_distinct_input_raw_collection.
Print Assumptions actual_raw_collection_template_certificates.





