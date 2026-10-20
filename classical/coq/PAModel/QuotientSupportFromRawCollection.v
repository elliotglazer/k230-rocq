(** Raw Collection support yields the forward half of the quotient image
    property. The raw support premise is an actual universal proof; it is
    never assumed to be a quotient image theorem. *)
From PAModel Require Import Model FiniteCoding FiniteCRT FreshNames CodeDescent CodeExpressions NumericalProofs
  NumericalEquivalence NumericalVacuitySteps NumericalEnvironments NumericalContexts
  ContextualProofs ContextualPropositional StableContextSupport SourceBounded
  QuotationHygiene QuotationPayloads QuotationAtomRebase SupportedQuotientEnvironments
  RawQuotientAtomCongruence ReplacementMatrixQuotation NamedExistential NamedBinderFresh
  ContextualWitnessRules RawDmemWitness ActualCollectionSupport CollectionWitnessKernels.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Theorem quotient_support_from_raw_collection M phi count eb ec en cb cc cn
    marker marker_name t a c u y z k dom mem quotient thetaZ thetaY eq
    q domZ memZ eq0 child body source target exsource extarget support allsupport
    ob oc on ib ic ine :
  source_bounded M phi (succM M (succM M count)) ->
  raw_empty_marker_graph M t marker_name marker -> stable_context_support M cb cc cn marker ->
  coding_lt M (zeroM M) k -> quotation_safe M eb ec en k t ->
  coding_lt M a k -> coding_lt M u k -> coding_lt M y k -> coding_lt M z k ->
  quotient_pair_safe M t y c z ->
  membership_graph M t u dom -> membership_graph M u a mem ->
  quotation_atom M false u a t k quotient -> quotation_atom M true y z t k eq ->
  binary_matrix_quotation M phi eb ec en u z k t thetaZ ->
  binary_matrix_quotation M phi eb ec en u y k t thetaY ->
  raw_dmem_witness_graph M t y c z q domZ memZ eq0 child body ->
  code_relation M (collection_support_parameters M dom mem quotient thetaZ thetaY eq)
    (support_input (CEvar 0) (CEvar 1) (CEvar 3)) source ->
  code_relation M (collection_support_parameters M dom mem quotient thetaZ thetaY eq)
    (support_output (CEvar 0) (CEvar 2) (CEvar 4)) target ->
  named_exists_graph M u source exsource -> named_exists_graph M u target extarget ->
  implication_graph M child exsource support -> universal_graph M z support allsupport ->
  named_binder_absent M support z -> stable_context_support M cb cc cn allsupport ->
  context_fresh M cb cc cn z -> formula_fresh M extarget z ->
  environment_cons M cb cc cn body ob oc on -> context_fresh M ob oc on u ->
  environment_cons M ob oc on source ib ic ine ->
  contextually_provable M cb cc cn q -> contextually_provable M cb cc cn extarget.
Proof.
  intros HB HM PM HK0 HK HA HU HY HZ HS HD HMem HQ HE HThetaZ HThetaY
    HRaw GS GT HExS HExT HSupport HAll HAbsent PAll HFZ HFT HOuter HFU HInner PQ.
  destruct HRaw as [GDZ [GMZ [GE0 [GChild [GBody GEx]]]]].
  assert (HIncl : context_included M cb cc cn ob oc on).
  { intros f Hf;apply (proj2 (context_member_cons M cb cc cn body ob oc on f HOuter));now right. }
  assert (PBody : stable_context_support M ob oc on body).
  { apply stable_context_support_member.
    apply (proj2 (context_member_cons M cb cc cn body ob oc on body HOuter));now left. }
  assert (PE0 : stable_context_support M ob oc on eq0).
  { exact (stable_context_support_conjunction_right M ob oc on child eq0 body GBody PBody). }
  assert (PChild : contextually_provable M ob oc on child).
  { apply stable_context_support_here.
    exact (stable_context_support_conjunction_left M ob oc on child eq0 body GBody PBody). }
  assert (PE : stable_context_support M ob oc on eq).
  { apply (stable_context_support_equivalent M ob oc on eq0 eq);[|exact PE0].
    destruct HS as [HZ0 [HTZ [HYZ HCZ]]].
    exact (quotation_atom_rebase M true y z t (succM M z) k eq0 eq
      (coding_lt_trans M (zeroM M) z (succM M z) HZ0 (coding_lt_succ M z)) HK0
      (coding_lt_trans M y z (succM M z) HYZ (coding_lt_succ M z))
      (coding_lt_succ M z)
      (coding_lt_trans M t z (succM M z) HTZ (coding_lt_succ M z))
      HY HZ (proj1 HK) GE0 HE). }
  assert (PSource : contextually_provable M ob oc on exsource).
  { apply (contextual_mp M ob oc on child exsource support PChild);[|exact HSupport].
    apply (contextual_self_all_specialize M ob oc on z support allsupport HAbsent HAll).
    exact (PAll ob oc on HIncl). }
  apply (contextual_witness_bind M cb cc cn z body q extarget ob oc on HFZ HFT GEx HOuter PQ).
  exact (actual_collection_support_witness M phi count eb ec en ob oc on marker marker_name
    t a u y z k dom mem quotient thetaZ thetaY eq source target exsource extarget ib ic ine
    HB HM (stable_context_support_included M cb cc cn ob oc on marker HIncl PM)
    HK0 HK HA HU HY HZ HD HMem HQ HE HThetaZ HThetaY PE GS GT HFU HExS HExT HInner PSource).
Qed.

Print Assumptions quotient_support_from_raw_collection.
