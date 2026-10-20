(** The innermost emitted-closure request is an actual source proof.
    The original subset/witness closure and trace are the only proof inputs. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
  SetFormulaCodes SetSchemaConstructors SchemaConstructorBounds SourcePropositionalRebase SourceBounded SourceFiniteCutoffShift SourceNativeKMatrixMaps
  SourceEmittedClosureRecipe SourceUpperWitnessRecipes SourceUpperTraceRequest
  SourceTraceProfileShell SourceClosureMatrixSpecialization SourceUpperProofHelpers
  SourceSubsetClosedPoint SourceFiniteParameters SourceFiniteParameterProofs
  SourceSequents NumericalRenaming NumericalSourceFull NumericalContexts SourceContextTransport SourceBoundMonotone
  SourceTraceBounds SourceDerivedRules.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
Unset Implicit Arguments.

Theorem source_full_emitted_inner_request M cb cc cn phi n profile theta atom matrix body
    witness subsetclosed xb subset matB matC selected finalbody target :
  source_bounded M phi (succM M (succM M n)) ->
  numerical_renaming M phi (code_numeral M 3)(code_numeral M 1)(code_numeral M 2)
    (code_numeral M 6) matrix ->
  sf_relation M SFMember (zeroM M)(code_numeral M 7) atom ->
  sf_relation M SFAnd atom matrix body -> sf_relation M SFEx body (zeroM M) theta ->
  source_trace_profile_shell M theta (code_numeral M 4)(code_numeral M 5) profile ->
  source_upper_witness_closed_recipe M phi (code_numeral M 6)(code_numeral M 5) witness ->
  code_relation M (schema_env3 (code_numeral M 5)(code_numeral M 3)(code_numeral M 1))
    (source_parameter_expression source_three_parameter_names (source_point_subset_closed $0)) subsetclosed ->
  code_relation M (schema_env3 (code_numeral M 5)(code_numeral M 3)(code_numeral M 1))
    (source_parameter_expression source_three_parameter_names ($1 ∈' $0)) xb ->
  code_relation M (schema_env3 (code_numeral M 5)(code_numeral M 3)(code_numeral M 1))
    (source_parameter_expression source_three_parameter_names (source_point_raw_subset $2 $1)) subset ->
  source_native_k_matrix M NativeKB phi matB ->source_native_k_matrix M NativeKC phi matC ->
  sf_relation M SFAnd matC selected finalbody ->
  sf_relation M SFMember (zeroM M)(code_numeral M 5) selected ->
  sf_relation M SFEx finalbody (zeroM M) target ->
  source_full_prv M cb cc cn subsetclosed ->source_full_prv M cb cc cn witness ->
  source_full_prv M cb cc cn profile ->source_full_prv M cb cc cn xb ->
  source_full_prv M cb cc cn subset ->source_full_prv M cb cc cn matB ->
  source_full_prv M cb cc cn target.
Proof.
  intros HP HM HA HB HE HProfile HW HSC HXB HSub HMB HMC HFinal HSelected HTarget
    PSC PW PProfile PXB PSub PMB.
  destruct (sf_relation_total M SFMember (code_numeral M 1)(code_numeral M 5)) as [ub HUb].
  assert (HUbCode:code_relation M
    (schema_env3 (code_numeral M 5)(code_numeral M 3)(code_numeral M 1))
    (source_parameter_expression source_three_parameter_names ($2 ∈' $0)) ub).
  { exact (proj2 (schema_expression_graph M _ SFMember (CEvar 2)(CEvar 0)
      (code_numeral M 1)(code_numeral M 5) ub eq_refl eq_refl) HUb). }
  pose proof (numerical_subset_closed_point M cb cc cn _ subsetclosed xb subset ub
    HSC HXB HSub HUbCode PSC PXB PSub) as PUb.
  destruct (code_relation_total M (E_upper_matrix_request (CEvar 0)(CEvar 1))
    (schema_env3 matC (code_numeral M 4)(code_numeral M 4))) as [request HRequestCode].
  pose proof (source_native_C_request_recipe M phi matC request HMC HRequestCode) as HRequest.
  pose proof (source_full_upper_trace_request M cb cc cn phi (succM M (succM M n))
    (code_numeral M 6)(code_numeral M 4)(code_numeral M 5) profile theta atom matrix body
    witness (code_numeral M 1) ub request HP HM HA HB HE HProfile HW HUb HRequest PW PProfile PUb) as PR.
  destruct (source_upper_matrix_request_shell M matC (code_numeral M 4) request HRequestCode)
    as (member & pair & some & bounded & HMember & HPair & HSome & HBounded & HImp).
  assert (WSome:source_sequent_wf M cb cc cn some).
  { pose proof (source_native_k_matrix_bound M NativeKC phi matC n HP HMC) as HC.
    cbn [native_k_tail native_k_delta source_succ_iter] in HC.
    destruct (source_full_prv_wellformed M cb cc cn matB PMB) as [j [_ HCtx]].
    apply (source_wf_transport_context M (zeroM M)(zeroM M)(zeroM M) some cb cc cn).
    - exists (succM M (succM M (succM M (succM M (succM M (succM M n)))))). split.
      + exact (proj2 (source_bounded_accept_unary M SFEx matC some _ (or_intror eq_refl) HSome) HC).
      + intros f HF. exfalso. exact (context_empty M (zeroM M)(zeroM M) f HF).
    - now exists j. }
  pose proof (full_source_ExI M cb cc cn matC some (zeroM M) matB WSome PMB HSome
    (source_native_C_instantiates_B M phi (succM M (succM M n)) matC matB HP HMC HMB)) as PSome.
  pose proof (source_full_modus_ponens M cb cc cn some bounded request HImp PR PSome) as PBounded.
  pose proof (sf_relation_functional M SFMember (zeroM M)(code_numeral M 5) member selected
    HMember HSelected) as E. subst member.
  exact (source_full_exists_conjunction_swap M cb cc cn selected matC pair finalbody bounded target
    HPair HFinal HBounded HTarget PBounded).
Qed.

Print Assumptions source_full_emitted_inner_request.
