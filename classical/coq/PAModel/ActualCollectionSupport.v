(** The support half of the Collection witness argument, using actual
    source-matrix invariance and actual raw-membership introduction. *)
From PAModel Require Import Model FiniteCoding CodeDescent CodeExpressions NumericalProofs
  NumericalEquivalence NumericalVacuitySteps NumericalEnvironments NumericalContexts ContextualProofs StableContextSupport
  SourceBounded QuotationHygiene QuotationPayloads SupportedQuotientEnvironments
  RawQuotientAtomCongruence ReplacementMatrixQuotation RawLawGraphs RawMembershipIntroLift
  StableBinaryInvariance CollectionWitnessKernels NamedExistential.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Definition collection_support_parameters M (dom mem quotient thetaZ thetaY eq:carrier M) :=
  dom .: mem .: quotient .: thetaZ .: thetaY .: eq .: fun _=>zeroM M.

Theorem actual_collection_support_witness M phi count eb ec en cb cc cn
    marker marker_name t a u y z k dom mem quotient thetaZ thetaY eq
    source target exsource extarget db dc dn :
  source_bounded M phi (succM M (succM M count)) ->
  raw_empty_marker_graph M t marker_name marker -> stable_context_support M cb cc cn marker ->
  coding_lt M (zeroM M) k -> quotation_safe M eb ec en k t ->
  coding_lt M a k -> coding_lt M u k -> coding_lt M y k -> coding_lt M z k ->
  membership_graph M t u dom -> membership_graph M u a mem ->
  quotation_atom M false u a t k quotient -> quotation_atom M true y z t k eq ->
  binary_matrix_quotation M phi eb ec en u z k t thetaZ ->
  binary_matrix_quotation M phi eb ec en u y k t thetaY ->
  stable_context_support M cb cc cn eq ->
  code_relation M (collection_support_parameters M dom mem quotient thetaZ thetaY eq)
    (support_input (CEvar 0) (CEvar 1) (CEvar 3)) source ->
  code_relation M (collection_support_parameters M dom mem quotient thetaZ thetaY eq)
    (support_output (CEvar 0) (CEvar 2) (CEvar 4)) target ->
  context_fresh M cb cc cn u -> named_exists_graph M u source exsource ->
  named_exists_graph M u target extarget -> environment_cons M cb cc cn source db dc dn ->
  contextually_provable M cb cc cn exsource -> contextually_provable M cb cc cn extarget.
Proof.
  intros HB HM PM HK0 HK HA HU HY HZ HD HMem HQ HE HThetaZ HThetaY PE
    GS GT HF HExS HExT HC PEx.
  set (rho:=collection_support_parameters M dom mem quotient thetaZ thetaY eq).
  destruct (code_relation_total M (E_wim (CEvar 0) (E_wim (CEvar 1) (CEvar 2))) rho)
    as [intro GI].
  destruct (code_relation_total M (E_wim (CEvar 3) (CEvar 4)) rho) as [arrow GA].
  destruct (code_relation_total M (E_wim (CEvar 5) (E_wim (CEvar 3) (CEvar 4))) rho)
    as [transport GP].
  assert (PI : stable_context_support M cb cc cn intro).
  { apply (stable_context_support_implies M cb cc cn marker intro);[|exact PM].
    destruct HM as [HN [HTN HM]].
    apply (actual_raw_membership_intro M t marker_name marker u a k dom mem quotient intro
      HN HTN HM HK0 (proj1 HK) HU HA HD HMem HQ).
    exact GI. }
  assert (GA' : implication_graph M thetaZ thetaY arrow).
  { exact (proj1 (expression_implication_iff M rho (CEvar 3) (CEvar 4)
      thetaZ thetaY arrow eq_refl eq_refl) GA). }
  assert (GP' : implication_graph M eq arrow transport).
  { exact (proj1 (expression_implication_iff M rho (CEvar 5) (E_wim (CEvar 3) (CEvar 4))
      eq arrow transport eq_refl GA) GP). }
  assert (PT : stable_context_support M cb cc cn transport).
  { exact (stable_binary_one_argument_implication M true phi count eb ec en
      u y u z y z k k t cb cc cn marker marker_name k eq thetaY thetaZ arrow transport
      HB HM PM (or_intror (conj eq_refl (conj eq_refl eq_refl)))
      (conj HK0 (conj (proj1 HK) (conj HY HZ))) HE HK HK HU HY HU HZ
      HThetaY HThetaZ GA' GP'). }
  exact (numerical_collection_support_witness M cb cc cn rho u source target exsource extarget
    eq intro transport db dc dn GS GT eq_refl GI GP PE PI PT HF HExS HExT HC PEx).
Qed.

Print Assumptions actual_collection_support_witness.
