(** Consume the carrier-bound premises in the final native coordinates.
    Internally coded proof and context pullback discharge the intermediate
    normalization context rather than asking the caller to construct it. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  SetFormulaCodes SourceBounded SourceFiniteCutoffShift SourceNativeKRecipes
  SourceNativeUpperFromCarrier SourceTranspositionProofTransport SourceZeroTransposition
  SourceUpperPremiseBounds SourceUpperTraceProfile SourceUpperTraceFrame SourceUpperWitnessRecipes
  NumericalRenaming NumericalContexts NumericalContextRenaming NumericalSourceFull.
Unset Implicit Arguments.

Theorem source_full_native_upper_from_bound_images M cb cc cn phi phi' n fresh b c
    profile exprofile witness subsetclosed xb pb
    imageEx imageWitness imageSubset imageX imageP target :
  source_bounded M phi (succM M (succM M n)) ->source_cutoff_shift M 2 phi phi' ->
  coding_lt M (succM M (succM M n)) fresh ->source_zero_transposition M fresh b c ->
  source_upper_trace_profile M phi' profile ->sf_relation M SFEx profile (zeroM M) exprofile ->
  source_upper_witness_closed_recipe M phi' (code_numeral M 1)(zeroM M) witness ->
  source_subset_closed_graph M (zeroM M) subsetclosed ->
  sf_relation M SFMember fresh (zeroM M) xb ->sf_relation M SFMember (code_numeral M 1)(zeroM M) pb ->
  numerical_renaming M exprofile b c (succM M fresh)(zeroM M) imageEx ->
  numerical_renaming M witness b c (succM M fresh)(zeroM M) imageWitness ->
  numerical_renaming M subsetclosed b c (succM M fresh)(zeroM M) imageSubset ->
  numerical_renaming M xb b c (succM M fresh)(zeroM M) imageX ->
  numerical_renaming M pb b c (succM M fresh)(zeroM M) imageP ->
  source_upper_conclusion_recipe M phi target ->
  source_full_prv M cb cc cn imageEx ->source_full_prv M cb cc cn imageWitness ->
  source_full_prv M cb cc cn imageSubset ->source_full_prv M cb cc cn imageX ->
  source_full_prv M cb cc cn imageP ->source_full_prv M cb cc cn target.
Proof.
  intros HP HS HF HM HProfile HEx HW HSC HXB HPB REx RW RS RX RP HT PEx PW PS PX PP.
  pose proof (source_cutoff_shift_bounded M 2 phi phi' n HP HS) as HP'.
  destruct (context_renaming_total M cb cc cn b c (succM M fresh)(zeroM M)) as [db [dc HC]].
  destruct (source_full_prv_wellformed M cb cc cn imageEx PEx) as [j [_ HCtx]].
  pose proof (source_zero_transposition_context_reverse M fresh b c cb cc cn db dc j HM HCtx HC) as HBack.
  pose proof (source_upper_trace_profile_bound M phi' profile (succM M n) HP' HProfile) as BProfile.
  pose proof (proj2 (source_bounded_accept_unary M SFEx profile exprofile
    (succM M (succM M n))(or_intror eq_refl) HEx) BProfile) as BEx.
  pose proof (source_upper_witness_carrier_bound M phi' witness (succM M n) HP' HW) as BW.
  pose proof (source_subset_carrier_bound M subsetclosed HSC) as BS.
  assert (BX:source_bounded M xb (succM M fresh)).
  { apply (proj2 (source_bounded_accept_atom M SFMember fresh (zeroM M) xb
      (succM M fresh)(or_introl eq_refl) HXB)). split;[apply coding_lt_succ|apply coding_zero_lt_succ]. }
  assert (BP:source_bounded M pb (code_numeral M 2)).
  { apply (proj2 (source_bounded_accept_atom M SFMember (code_numeral M 1)(zeroM M) pb
      (code_numeral M 2)(or_introl eq_refl) HPB)). split;[apply coding_lt_succ|apply coding_zero_lt_succ]. }
  pose proof (source_zero_transposition_proof_pullback M fresh b c cb cc cn db dc exprofile imageEx
    (succM M (succM M n)) HM BEx REx HC PEx) as PEx'.
  pose proof (source_zero_transposition_proof_pullback M fresh b c cb cc cn db dc witness imageWitness
    (succM M (succM M n)) HM BW RW HC PW) as PW'.
  pose proof (source_zero_transposition_proof_pullback M fresh b c cb cc cn db dc subsetclosed imageSubset
    (code_numeral M 1) HM BS RS HC PS) as PS'.
  pose proof (source_zero_transposition_proof_pullback M fresh b c cb cc cn db dc xb imageX
    (succM M fresh) HM BX RX HC PX) as PX'.
  pose proof (source_zero_transposition_proof_pullback M fresh b c cb cc cn db dc pb imageP
    (code_numeral M 2) HM BP RP HC PP) as PP'.
  exact (source_full_native_upper_from_carrier M db dc cn cb cc phi phi' n fresh b c
    profile exprofile witness subsetclosed xb pb target HP HS HF HM HBack HProfile HEx HW HSC HXB HPB HT
    PEx' PW' PS' PX' PP').
Qed.

Print Assumptions source_full_native_upper_from_bound_images.
