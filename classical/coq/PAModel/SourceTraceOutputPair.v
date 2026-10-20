(** The same trace container supplies the output-root implication and
    emitted closure. The arbitrary predicate matrix is a real substitution. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes
  SourceBounded SourceUpperTraceProfile SourceUpperTraceMember SourceUpperTraceEmittedClosure
  SourceUpperTraceFrame SourceUpperWitnessRecipes SourceEmittedClosureRecipe SourceUpperProofHelpers
  SourceEmittedFrameRequest SourceRoleReopening NumericalSubstitution NumericalSourceFull
  NumericalContexts NumericalEnvironments SourceContextTransport SourceBoundMonotone SourceSequents SourceRenamingWellformedness SourceRenamingBounds
  NumericalRenaming RenamingSubstitution.
Unset Implicit Arguments.

Theorem source_full_trace_output_pair M cb cc cn phi n profile witness subsetclosed x p
    xc xb pb rb rc value emitted root pair :
  source_bounded M phi (succM M (succM M n)) ->source_upper_trace_profile M phi profile ->
  source_upper_witness_closed_recipe M phi (code_numeral M 2)(code_numeral M 1) witness ->
  source_subset_closed_graph M (code_numeral M 1) subsetclosed ->
  sf_relation M SFMember x (zeroM M) xc ->sf_relation M SFMember x (code_numeral M 1) xb ->
  sf_relation M SFMember p (code_numeral M 1) pb ->source_role_reopening M p x rb rc ->
  numerical_substitution M phi rb rc (code_numeral M 2)(code_numeral M 2) value ->
  source_emitted_closure_recipe M phi emitted ->sf_relation M SFImpl value xc root ->
  sf_relation M SFAnd root emitted pair ->
  source_full_prv M cb cc cn subsetclosed ->source_full_prv M cb cc cn witness ->
  source_full_prv M cb cc cn profile ->source_full_prv M cb cc cn xb ->source_full_prv M cb cc cn pb ->
  source_full_prv M cb cc cn pair.
Proof.
  intros HP HProfile HW HSC HXC HXB HPB HMap HValue HEmitted HRoot HPair PSC PW PP PXB PPB.
  pose proof (source_full_upper_trace_emitted_closure M cb cc cn phi n profile witness subsetclosed emitted
    HP HProfile HW HSC HEmitted PSC PW PP) as PE.
  destruct (source_full_prv_wellformed M cb cc cn xb PXB) as [kx [BX HC]].
  destruct (source_full_prv_wellformed M cb cc cn pb PPB) as [kp [BP _]].
  destruct (source_renaming_range_bound M rb rc (code_numeral M 2)
    (zeroM M)(succM M (succM M n))) as [kv HRange].
  assert (BValue:source_bounded M value kv).
  { apply (numerical_renaming_preserves_bound M phi rb rc (code_numeral M 2)(zeroM M)
      value (succM M (succM M n)) kv HP);[|exact HRange].
    apply (proj2 (numerical_renaming_substitution M phi rb rc (code_numeral M 2)(zeroM M) value)).
    now rewrite coding_add_zero_r. }
  destruct (environment_cons_total M cb cc cn value) as [ub [uc [un HCons]]].
  destruct (source_full_assume M cb cc cn value ub uc un
    (source_wf_from_finite M cb cc cn value kv BValue ltac:(now exists kx)) HCons) as [FU PV].
  pose proof (source_full_weaken_cons_finite M cb cc cn value ub uc un subsetclosed HCons FU PSC) as PSC'.
  pose proof (source_full_weaken_cons_finite M cb cc cn value ub uc un witness HCons FU PW) as PW'.
  pose proof (source_full_weaken_cons_finite M cb cc cn value ub uc un profile HCons FU PP) as PP'.
  pose proof (source_full_weaken_cons_finite M cb cc cn value ub uc un xb HCons FU PXB) as PXB'.
  pose proof (source_full_weaken_cons_finite M cb cc cn value ub uc un pb HCons FU PPB) as PPB'.
  pose proof (source_full_upper_trace_member M ub uc un phi n profile x p xc xb pb value rb rc
    HP HProfile HXC HXB HPB HMap HValue PP' PXB' PPB' PV) as PXC.
  pose proof (source_full_implication_intro M cb cc cn value xc root ub uc un HCons HRoot PXC) as PR.
  exact (source_full_conjunction M cb cc cn root emitted pair HPair PR PE).
Qed.

Print Assumptions source_full_trace_output_pair.
