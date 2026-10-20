(** The two inner universal requests in emitted_closure, with actual
    context shifts and literal source introductions. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
  SetFormulaCodes SetSchemaConstructors SourceBounded SourceNativeKMatrixMaps
  SourceUpperTraceFrame SourceEmittedFrameRequest SourceUpperProofHelpers
  SourceSubsetClosedPoint SourceFiniteParameters SourceFiniteParameterProofs
  NumericalSourceFull NumericalContexts NumericalEnvironments NumericalContextRenaming
  NumericalRenaming SourceQuantifierRules SourceProofRenaming SourceContextTransport SourceSequents.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
Unset Implicit Arguments.

Theorem source_full_emitted_inner_universals M cb cc cn phi n allU subset uimp allY yimp
    matB matC selected finalbody target subset' kU :
  source_upper_trace_frame M cb cc cn phi (succM M (succM M n))
    (code_numeral M 4)(code_numeral M 2)(code_numeral M 3)(code_numeral M 1) ->
  source_bounded M allU kU ->
  sf_relation M SFAll uimp (zeroM M) allU ->sf_relation M SFImpl subset allY uimp ->
  sf_relation M SFAll yimp (zeroM M) allY ->sf_relation M SFImpl matB target yimp ->
  source_native_k_matrix M NativeKB phi matB ->source_native_k_matrix M NativeKC phi matC ->
  sf_relation M SFAnd matC selected finalbody ->
  sf_relation M SFMember (zeroM M)(code_numeral M 5) selected ->
  sf_relation M SFEx finalbody (zeroM M) target ->
  source_formula_shift M subset subset' ->
  code_relation M (schema_env3 (code_numeral M 5)(code_numeral M 3)(code_numeral M 1))
    (source_parameter_expression source_three_parameter_names (source_point_raw_subset $2 $1)) subset' ->
  source_full_prv M cb cc cn allU.
Proof.
  intros Frame HU HAllU HImpU HAllY HImpY HMB HMC HFinal HSelected HTarget HSubShift HSubCode.
  pose proof (source_upper_trace_frame_context_finite M cb cc cn phi (succM M (succM M n))
    (code_numeral M 4)(code_numeral M 2)(code_numeral M 3)(code_numeral M 1) Frame) as FC.
  pose proof (proj1 (source_bounded_accept_unary M SFAll uimp allU kU (or_introl eq_refl) HAllU) HU) as BImpU.
  pose proof (proj1 (source_bounded_accept_binary M SFImpl subset allY uimp (succM M kU)
    (or_intror (or_intror eq_refl)) HImpU) BImpU) as BPartsU.
  destruct BPartsU as [BSubset BAllY].
  pose proof (proj1 (source_bounded_accept_unary M SFAll yimp allY (succM M kU)
    (or_introl eq_refl) HAllY) BAllY) as BImpY.
  pose proof (proj1 (proj1 (source_bounded_accept_binary M SFImpl matB target yimp
    (succM M (succM M kU))(or_intror (or_intror eq_refl)) HImpY) BImpY)) as BMatB.
  destruct (context_shift_total M cb cc cn) as [ub [uc HSU]].
  pose proof (source_context_finite_bound_shift M cb cc cn ub uc FC HSU) as FU.
  pose proof (source_upper_trace_frame_shift M cb cc cn phi (succM M (succM M n))
    (code_numeral M 4)(code_numeral M 2)(code_numeral M 3)(code_numeral M 1) ub uc Frame HSU) as FrameU.
  destruct (environment_cons_total M ub uc cn subset) as [gb [gc [gn HCG]]].
  destruct (source_full_assume M ub uc cn subset gb gc gn
    (source_wf_from_finite M ub uc cn subset (succM M kU) BSubset FU) HCG) as [FG PG].
  pose proof (source_upper_trace_frame_weaken M ub uc cn phi (succM M (succM M n))
    (code_numeral M 5)(code_numeral M 3)(code_numeral M 4)(code_numeral M 2)
    subset gb gc gn FrameU HCG FG) as FrameG.
  destruct (context_shift_total M gb gc gn) as [yb [yc HSY]].
  pose proof (source_context_finite_bound_shift M gb gc gn yb yc FG HSY) as FY.
  pose proof (source_upper_trace_frame_shift M gb gc gn phi (succM M (succM M n))
    (code_numeral M 5)(code_numeral M 3)(code_numeral M 4)(code_numeral M 2) yb yc FrameG HSY) as FrameY.
  pose proof (source_full_prv_renaming M gb gc gn subset (zeroM M)(zeroM M)(zeroM M)
    (code_numeral M 1) yb yc subset' PG HSY HSubShift) as PSubY.
  destruct (environment_cons_total M yb yc gn matB) as [hb [hc [hn HCB]]].
  destruct (source_full_assume M yb yc gn matB hb hc hn
    (source_wf_from_finite M yb yc gn matB (succM M (succM M kU)) BMatB FY) HCB) as [FH PMB].
  pose proof (source_upper_trace_frame_weaken M yb yc gn phi (succM M (succM M n))
    (code_numeral M 6)(code_numeral M 4)(code_numeral M 5)(code_numeral M 3)
    matB hb hc hn FrameY HCB FH) as FrameH.
  pose proof (source_full_weaken_cons_finite M yb yc gn matB hb hc hn subset' HCB FH PSubY) as PSubH.
  pose proof (source_full_frame_emitted_inner_request M hb hc hn phi n subset' matB matC selected finalbody target
    FrameH HSubCode HMB HMC HFinal HSelected HTarget PSubH PMB) as PTarget.
  pose proof (source_full_implication_intro M yb yc gn matB target yimp hb hc hn HCB HImpY PTarget) as PImpY.
  pose proof (source_full_all_intro M gb gc gn yimp allY yb yc FG HSY HAllY PImpY) as PAllY.
  pose proof (source_full_implication_intro M ub uc cn subset allY uimp gb gc gn HCG HImpU PAllY) as PImpU.
  exact (source_full_all_intro M cb cc cn uimp allU ub uc FC HSU HAllU PImpU).
Qed.

Print Assumptions source_full_emitted_inner_universals.
