(** The actual carrier proof produces the exact native upper conclusion
    after a checked internally finite transposition. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  SourceBounded SourceFiniteCutoffShift SourceNativeKRecipes SourceUpperCarrierNormalization
  SourceZeroTransposition SourceCarrierRenaming SourceBoundedOutputRoot SourceZFROutputRoot
  SourceUpperTraceProfile SourceUpperWitnessRecipes SourceUpperTraceFrame
  SetFormulaCodes NumericalRenaming NumericalContexts NumericalContextRenaming NumericalSourceFull SourceProofRenaming
  SourceDescriptorClosure SourceZFRProvability SourceSetTheoryDescriptors.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Theorem source_zero_transposition_positive_fixes M fresh b c :
  source_zero_transposition M fresh b c ->carrier_positive_fixes M fresh b c (succM M fresh).
Proof.
  intros HM i H0 HI. apply (source_zero_transposition_other M fresh b c i HM H0).
  intro E. subst i. exact (@Peano.lt_neq (carrier M)(raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) fresh fresh HI eq_refl).
Qed.

Theorem source_upper_recipe_zero_transposition M phi phi' n fresh b c before after :
  source_bounded M phi (succM M (succM M n)) ->source_cutoff_shift M 2 phi phi' ->
  coding_lt M (succM M (succM M n)) fresh ->source_zero_transposition M fresh b c ->
  source_trace_output_root_recipe M phi' fresh (code_numeral M 1) before ->
  source_upper_conclusion_recipe M phi after ->
  numerical_renaming M before b c (succM M fresh)(zeroM M) after.
Proof.
  intros HP HS HB HM HF HA.
  exact (source_upper_recipe_carrier_normalization M phi phi' n fresh b c (succM M fresh) before after
    HP HS HB (source_zero_transposition_name M fresh b c HM)
    (source_zero_transposition_positive_fixes M fresh b c HM) HF HA).
Qed.

Theorem source_full_native_upper_from_carrier M cb cc cn db dc phi phi' n fresh b c
    profile exprofile witness subsetclosed xb pb target :
  source_bounded M phi (succM M (succM M n)) ->source_cutoff_shift M 2 phi phi' ->
  coding_lt M (succM M (succM M n)) fresh ->source_zero_transposition M fresh b c ->
  context_renaming M cb cc cn b c (succM M fresh)(zeroM M) db dc ->
  source_upper_trace_profile M phi' profile ->sf_relation M SFEx profile (zeroM M) exprofile ->
  source_upper_witness_closed_recipe M phi' (code_numeral M 1)(zeroM M) witness ->
  source_subset_closed_graph M (zeroM M) subsetclosed ->
  sf_relation M SFMember fresh (zeroM M) xb ->sf_relation M SFMember (code_numeral M 1)(zeroM M) pb ->
  source_upper_conclusion_recipe M phi target ->
  source_full_prv M cb cc cn exprofile ->source_full_prv M cb cc cn witness ->
  source_full_prv M cb cc cn subsetclosed ->source_full_prv M cb cc cn xb ->
  source_full_prv M cb cc cn pb ->source_full_prv M db dc cn target.
Proof.
  intros HP HS HB HM HC HProfile HEx HW HSC HXB HPB HT PEx PW PSC PXB PPB.
  pose proof (source_cutoff_shift_bounded M 2 phi phi' n HP HS) as HP'.
  destruct (source_trace_output_root_recipe_total M phi' fresh (code_numeral M 1)) as [before HF].
  pose proof (source_full_bounded_output_root M cb cc cn phi' (succM M n) profile exprofile witness subsetclosed
    fresh (code_numeral M 1) xb pb before HP' HProfile HEx HW HSC HXB HPB HF PEx PW PSC PXB PPB) as PBefore.
  exact (source_full_prv_renaming M cb cc cn before b c (succM M fresh)(zeroM M) db dc target
    PBefore HC (source_upper_recipe_zero_transposition M phi phi' n fresh b c before target HP HS HB HM HF HT)).
Qed.

Theorem source_zfr_native_upper_from_carrier M phi phi' n fresh b c witness subsetclosed xb pb target :
  source_bounded M phi (succM M (succM M n)) ->source_cutoff_shift M 2 phi phi' ->
  coding_lt M (succM M (succM M n)) fresh ->source_zero_transposition M fresh b c ->
  source_upper_witness_closed_recipe M phi' (code_numeral M 1)(zeroM M) witness ->
  source_subset_closed_graph M (zeroM M) subsetclosed ->
  sf_relation M SFMember fresh (zeroM M) xb ->sf_relation M SFMember (code_numeral M 1)(zeroM M) pb ->
  source_upper_conclusion_recipe M phi target ->
  source_zfr_provable M witness ->source_zfr_provable M subsetclosed ->
  source_zfr_provable M xb ->source_zfr_provable M pb ->source_zfr_provable M target.
Proof.
  intros HP HS HB HM HW HSC HXB HPB HT PW PSC PXB PPB.
  pose proof (source_cutoff_shift_bounded M 2 phi phi' n HP HS) as HP'.
  destruct (source_zfr_bounded_output_root_total M phi' (succM M n) witness subsetclosed
    fresh (code_numeral M 1) xb pb HP' HW HSC HXB HPB PW PSC PXB PPB) as [before [HF PBefore]].
  apply (proj1 (source_zfr_descriptor_provable M target)).
  exact (source_descriptor_provable_renaming M ZFRSourceDescriptor before b c (succM M fresh)(zeroM M) target
    (proj2 (source_zfr_descriptor_provable M before) PBefore)
    (source_upper_recipe_zero_transposition M phi phi' n fresh b c before target HP HS HB HM HF HT)).
Qed.

Print Assumptions source_upper_recipe_zero_transposition.
Print Assumptions source_full_native_upper_from_carrier.
Print Assumptions source_zfr_native_upper_from_carrier.
