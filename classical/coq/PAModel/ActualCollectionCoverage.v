(** Functional uniqueness is specialized inside the collected-witness
    branch, where its domain guard is available. No witness is extracted
    semantically from a numerical existential proof. *)
From PAModel Require Import Model FiniteCoding CodeDescent CodeExpressions NumericalProofs
  NumericalEquivalence NumericalVacuitySteps NumericalEnvironments NumericalContexts ContextualProofs
  ContextualPropositional StableContextSupport SourceBounded NumericalQuotation
  QuotationHygiene QuotationPayloads SetFormulaCodes SetSchemaConstructors SchemaRenamingDescriptors
  ReplacementMatrixQuotation FunctionalitySpecialization NamedExistential ContextualWitnessRules
  CollectionWitnessKernels ProofTemplates TemplatePropositional.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Definition collection_coverage_parameters M (dom mem thetaZ thetaY eq:carrier M) :=
  dom .: mem .: thetaZ .: thetaY .: eq .: fun _=>zeroM M.

Theorem actual_collection_coverage_witness M phi bound ra rb functionSource functionQ
    eb ec en oldbase fresh t cb cc cn u y z du dy dz mem thetaY thetaZ eq
    source target exsource extarget db dc dn :
  source_bounded M phi bound -> schema_renaming M RepA phi ra -> schema_renaming M RepB phi rb ->
  code_relation M (ra .: rb .: fun _=>zeroM M) (E_sf_functionality (CEvar 0) (CEvar 1)) functionSource ->
  quotation_safe M eb ec en oldbase t -> quotation_safe M eb ec en fresh t ->
  coding_lt M u fresh -> coding_lt M y fresh -> coding_lt M z fresh ->
  numerical_quotation M functionSource eb ec en oldbase t functionQ ->
  binary_matrix_quotation M phi eb ec en u y fresh t thetaY ->
  binary_matrix_quotation M phi eb ec en u z fresh t thetaZ ->
  quotation_atom M true y z t fresh eq ->
  membership_graph M t u du -> membership_graph M t y dy -> membership_graph M t z dz ->
  stable_context_support M cb cc cn functionQ -> stable_context_support M cb cc cn du ->
  stable_context_support M cb cc cn dy -> stable_context_support M cb cc cn thetaY ->
  code_relation M (collection_coverage_parameters M dz mem thetaZ thetaY eq)
    (coverage_input (CEvar 0) (CEvar 1) (CEvar 2)) source ->
  code_relation M (collection_coverage_parameters M dz mem thetaZ thetaY eq)
    (coverage_output (CEvar 0) (CEvar 1) (CEvar 4)) target ->
  context_fresh M cb cc cn z -> named_exists_graph M z source exsource ->
  named_exists_graph M z target extarget -> environment_cons M cb cc cn source db dc dn ->
  contextually_provable M cb cc cn exsource -> contextually_provable M cb cc cn extarget.
Proof.
  intros HB HA HBren HSource HOld HFresh HU HY HZ HFunction HThetaY HThetaZ HE HDU HDY HDZ
    PF PU PY PThetaY GS GT HF HExS HExT HC PEx.
  set (rho:=collection_coverage_parameters M dz mem thetaZ thetaY eq).
  apply (contextual_witness_map M cb cc cn z source target exsource extarget db dc dn
    HF HExS HExT HC PEx).
  assert (HI : context_included M cb cc cn db dc dn).
  { intros f Hf;apply (proj2 (context_member_cons M cb cc cn source db dc dn f HC));now right. }
  assert (PSource : stable_context_support M db dc dn source).
  { apply stable_context_support_member.
    apply (proj2 (context_member_cons M cb cc cn source db dc dn source HC));now left. }
  assert (PZ : stable_context_support M db dc dn dz).
  { apply (stable_context_support_derivation M db dc dn rho
      (cons (coverage_input (CEvar 0) (CEvar 1) (CEvar 2)) nil) (CEvar 0)).
    - intros e [<-|[]] f HG. assert (f=source) by exact (code_relation_functional M _ rho f source HG GS).
      now subst f.
    - apply template_der_andl with (b:=E_wa (CEvar 1) (CEvar 2)). apply dhyp;cbn;auto.
    - reflexivity. }
  destruct (code_relation_total M (E_wim (CEvar 2) (CEvar 4)) rho) as [inner GI].
  destruct (code_relation_total M (E_wim (CEvar 3) (E_wim (CEvar 2) (CEvar 4))) rho)
    as [uniqueness GUn].
  assert (GInner : quotation_binary M SFImpl thetaZ eq inner).
  { exact (proj1 (expression_implication_iff M rho (CEvar 2) (CEvar 4)
      thetaZ eq inner eq_refl eq_refl) GI). }
  assert (GU : quotation_binary M SFImpl thetaY inner uniqueness).
  { exact (proj1 (expression_implication_iff M rho (CEvar 3) (E_wim (CEvar 2) (CEvar 4))
      thetaY inner uniqueness eq_refl GI) GUn). }
  assert (PUn : stable_context_support M db dc dn uniqueness).
  { exact (stable_replacement_functionality_specialization M db dc dn phi bound ra rb functionSource
      eb ec en oldbase fresh t u y z functionQ thetaY thetaZ eq inner uniqueness du dy dz
      HB HA HBren HSource HOld HFresh HU HY HZ HFunction HThetaY HThetaZ HE GInner GU HDU HDY HDZ
      (stable_context_support_included M cb cc cn db dc dn functionQ HI PF)
      (stable_context_support_included M cb cc cn db dc dn du HI PU)
      (stable_context_support_included M cb cc cn db dc dn dy HI PY) PZ). }
  apply (contextual_propositional_sound M db dc dn rho
    (coverage_hypotheses (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4))
    (coverage_output (CEvar 0) (CEvar 1) (CEvar 4))).
  - intros e [<-|[<-|[<-|[]]]] f HG.
    + assert (f=source) by exact (code_relation_functional M _ rho f source HG GS).
      subst f;apply stable_context_support_here,PSource.
    + assert (f=thetaY) by exact HG. subst f;exact (PThetaY db dc dn HI).
    + assert (f=uniqueness) by exact (code_relation_functional M _ rho f uniqueness HG GUn).
      subst f;apply stable_context_support_here,PUn.
  - apply collection_coverage_program.
  - exact GT.
Qed.

Print Assumptions actual_collection_coverage_witness.
