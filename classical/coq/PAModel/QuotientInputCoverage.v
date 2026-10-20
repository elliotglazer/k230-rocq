(** Change a quotient-member input to a raw representative, then use
    raw Collection coverage and source functionality to recover membership. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeDescent CodeExpressions FreshNames
  NumericalProofs NumericalQuotation NumericalEquivalence NumericalVacuitySteps
  NumericalContexts NumericalEnvironments ContextualProofs ContextualWitnessRules
  StableContextSupport SourceBounded QuotationHygiene QuotationPayloads QuotationAtomRebase
  SetFormulaCodes SetSchemaConstructors SchemaRenamingDescriptors SupportedQuotientEnvironments
  RawQuotientAtomCongruence ReplacementMatrixQuotation NamedExistential NamedBinderFresh
  RawDmemWitness StableBinaryInvariance ActualCollectionCoverage QuotientCoverageFromRawCollection
  CollectionWitnessKernels.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Theorem quotient_coverage_from_quotient_input M phi count ra rb functionSource functionQ
    eb ec en oldbase t a c marker marker_name cb cc cn x u y z dy
    thetaXY thetaUY thetaUZ qInput du inA eq0 childInput bodyInput
    dz memZ eqYZ childOut target q source exsource has inner coverage allcoverage
    ob oc on ib ic ine :
  source_bounded M phi (succM M (succM M count)) ->
  schema_renaming M RepA phi ra -> schema_renaming M RepB phi rb ->
  code_relation M (ra .: rb .: fun _=>zeroM M) (E_sf_functionality (CEvar 0) (CEvar 1)) functionSource ->
  raw_empty_marker_graph M t marker_name marker -> stable_context_support M cb cc cn marker ->
  quotation_safe M eb ec en oldbase t -> quotation_safe M eb ec en z t ->
  quotient_pair_safe M t x a u -> coding_lt M u z -> coding_lt M y z ->
  numerical_quotation M functionSource eb ec en oldbase t functionQ ->
  binary_matrix_quotation M phi eb ec en x y (succM M z) t thetaXY ->
  binary_matrix_quotation M phi eb ec en u y (succM M z) t thetaUY ->
  binary_matrix_quotation M phi eb ec en u z (succM M z) t thetaUZ ->
  membership_graph M t y dy ->
  raw_dmem_witness_graph M t x a u qInput du inA eq0 childInput bodyInput ->
  raw_dmem_witness_graph M t y c z q dz memZ eqYZ childOut target ->
  code_relation M (collection_coverage_parameters M dz memZ thetaUZ thetaUY eqYZ)
    (coverage_input (CEvar 0) (CEvar 1) (CEvar 2)) source ->
  named_exists_graph M z source exsource -> quotation_quantifier M false z t thetaUZ has ->
  implication_graph M has exsource inner -> implication_graph M childInput inner coverage ->
  universal_graph M u coverage allcoverage -> named_binder_absent M coverage u ->
  stable_context_support M cb cc cn allcoverage -> stable_context_support M cb cc cn functionQ ->
  stable_context_support M cb cc cn dy -> stable_context_support M cb cc cn thetaXY ->
  context_fresh M cb cc cn u -> formula_fresh M q u ->
  environment_cons M cb cc cn bodyInput ob oc on -> context_fresh M ob oc on z ->
  environment_cons M ob oc on source ib ic ine ->
  contextually_provable M cb cc cn qInput -> contextually_provable M cb cc cn q.
Proof.
  intros HB HA HBren HSource HM PM HOld HSafe HS HU HY HFunction HThetaXY HThetaUY HThetaUZ
    HDY HRawInput HRawOut GS HExS HHas HInner HCoverage HAll HAbsent PAll PFunction PY PThetaXY
    HFU HFQ HOuter HFZ HInnerContext PInput.
  destruct HRawInput as [HDU [HInA [HE0 [HChild [HBody HExInput]]]]].
  assert (HI : context_included M cb cc cn ob oc on).
  { intros f Hf;apply (proj2 (context_member_cons M cb cc cn bodyInput ob oc on f HOuter));now right. }
  assert (PBody : stable_context_support M ob oc on bodyInput).
  { apply stable_context_support_member.
    apply (proj2 (context_member_cons M cb cc cn bodyInput ob oc on bodyInput HOuter));now left. }
  assert (PChild : stable_context_support M ob oc on childInput).
  { exact (stable_context_support_conjunction_left M ob oc on childInput eq0 bodyInput HBody PBody). }
  assert (PU : stable_context_support M ob oc on du).
  { exact (stable_context_support_conjunction_left M ob oc on du inA childInput HChild PChild). }
  assert (PInA : stable_context_support M ob oc on inA).
  { exact (stable_context_support_conjunction_right M ob oc on du inA childInput HChild PChild). }
  assert (PE0 : stable_context_support M ob oc on eq0).
  { exact (stable_context_support_conjunction_right M ob oc on childInput eq0 bodyInput HBody PBody). }
  destruct HS as [HU0 [HTU [HXU HAU]]].
  assert (HXZ : coding_lt M x z) by exact (coding_lt_trans M x u z HXU HU).
  assert (HZ0 : coding_lt M (zeroM M) z) by exact (coding_lt_trans M (zeroM M) u z HU0 HU).
  assert (HNext : quotation_safe M eb ec en (succM M z) t).
  { split.
    - exact (coding_lt_trans M t z (succM M z) (proj1 HSafe) (coding_lt_succ M z)).
    - intros i v HV;exact (coding_lt_trans M v z (succM M z) ((proj2 HSafe) i v HV) (coding_lt_succ M z)). }
  destruct (quotation_atom_total M true x u t (succM M z)) as [eq HE].
  assert (PE : stable_context_support M ob oc on eq).
  { apply (stable_context_support_equivalent M ob oc on eq0 eq);[|exact PE0].
    exact (quotation_atom_rebase M true x u t (succM M u) (succM M z) eq0 eq
      (coding_lt_trans M (zeroM M) u (succM M u) HU0 (coding_lt_succ M u))
      (coding_lt_trans M (zeroM M) z (succM M z) HZ0 (coding_lt_succ M z))
      (coding_lt_trans M x u (succM M u) HXU (coding_lt_succ M u)) (coding_lt_succ M u)
      (coding_lt_trans M t u (succM M u) HTU (coding_lt_succ M u))
      (coding_lt_trans M x z (succM M z) HXZ (coding_lt_succ M z))
      (coding_lt_trans M u z (succM M z) HU (coding_lt_succ M z)) (proj1 HNext) HE0 HE). }
  destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 1))
    (thetaXY .: thetaUY .: fun _=>zeroM M)) as [arrow GArrow].
  destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 1))
    (eq .: arrow .: fun _=>zeroM M)) as [transport GTransport].
  assert (PTransport : stable_context_support M ob oc on transport).
  { exact (stable_binary_one_argument_implication M false phi count eb ec en
      x y u y x u (succM M z) (succM M z) t ob oc on marker marker_name (succM M z)
      eq thetaXY thetaUY arrow transport HB HM
      (stable_context_support_included M cb cc cn ob oc on marker HI PM)
      (or_introl (conj eq_refl (conj eq_refl eq_refl)))
      (conj (coding_lt_trans M (zeroM M) z (succM M z) HZ0 (coding_lt_succ M z))
        (conj (proj1 HNext) (conj (coding_lt_trans M x z (succM M z) HXZ (coding_lt_succ M z))
          (coding_lt_trans M u z (succM M z) HU (coding_lt_succ M z))))) HE HNext HNext
      (coding_lt_trans M x z (succM M z) HXZ (coding_lt_succ M z))
      (coding_lt_trans M y z (succM M z) HY (coding_lt_succ M z))
      (coding_lt_trans M u z (succM M z) HU (coding_lt_succ M z))
      (coding_lt_trans M y z (succM M z) HY (coding_lt_succ M z))
      HThetaXY HThetaUY GArrow GTransport). }
  assert (PThetaUY : stable_context_support M ob oc on thetaUY).
  { apply (stable_context_support_mp M ob oc on thetaXY thetaUY arrow GArrow).
    - exact (stable_context_support_included M cb cc cn ob oc on thetaXY HI PThetaXY).
    - exact (stable_context_support_mp M ob oc on eq arrow transport GTransport PE PTransport). }
  apply (contextual_witness_bind M cb cc cn u bodyInput qInput q ob oc on HFU HFQ HExInput HOuter PInput).
  exact (quotient_coverage_from_raw_collection M phi (succM M (succM M count)) ra rb functionSource functionQ
    eb ec en oldbase t c ob oc on u y z du dy dz inA memZ thetaUY thetaUZ eqYZ source exsource
    q childOut target has childInput inner coverage allcoverage ib ic ine HB HA HBren HSource HOld
    HSafe HU HY HFunction HThetaUY HThetaUZ HDU HDY HRawOut GS HExS HHas HChild HInner HCoverage HAll HAbsent
    (stable_context_support_included M cb cc cn ob oc on allcoverage HI PAll)
    (stable_context_support_included M cb cc cn ob oc on functionQ HI PFunction) PU
    (stable_context_support_included M cb cc cn ob oc on dy HI PY) PInA PThetaUY HFZ HInnerContext).
Qed.

Print Assumptions quotient_coverage_from_quotient_input.
