(** Literal fresh-carrier images of the five native carrier premises. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
 SourceBounded SourceFiniteCutoffShift SourceUpperWitnessRecipes SourceUpperTraceFrame
 SourceNativeRelativeCarrier SourceNativeWitnessCarrierRenaming SourceZeroTransposition
 NumericalRenaming NumericalRenamingMaps SourceRelativization.
Unset Implicit Arguments.
Theorem source_native_relative_premise_graphs M domain phi shifted n fresh b c
 exprofile witness subsetclosed xb pb ie iw iset ix ip re rw rs:
 source_bounded M phi(succM M(succM M n))->source_cutoff_shift M 2 phi shifted->
 coding_lt M(succM M(succM M n))fresh->source_zero_transposition M fresh b c->
 source_upper_witness_closed_recipe M shifted(code_numeral M 1)(zeroM M)witness->
 source_upper_witness_closed_recipe M shifted(code_numeral M 1)fresh iw->
 source_subset_closed_graph M(zeroM M)subsetclosed->source_subset_closed_graph M fresh iset->
 sf_relation M SFMember fresh(zeroM M)xb->sf_relation M SFMember(code_numeral M 1)(zeroM M)pb->
 sf_relation M SFMember(zeroM M)fresh ix->sf_relation M SFMember(code_numeral M 1)fresh ip->
 numerical_renaming M exprofile b c(succM M fresh)(zeroM M)ie->
 source_relativization M domain ie re->source_relativization M domain iw rw->source_relativization M domain iset rs->
 source_native_carrier_relative_premises M domain fresh b c exprofile witness subsetclosed xb pb re rw rs ix ip.
Proof.
 intros BP HCut HF HTrans HW HW' HS HS' HXB HPB HIX HIP RE HRE HRW HRS.
 assert(HOne:coding_lt M(code_numeral M 1)fresh).
 { apply(coding_lt_trans M(code_numeral M 1)(succM M(succM M n))fresh);[|exact HF].
   apply(proj2(coding_lt_succ_cancel M(zeroM M)(succM M n))). apply coding_zero_lt_succ. }
 assert(H1Z:code_numeral M 1<>zeroM M).
 { intro E. pose proof(coding_zero_lt_succ M(zeroM M))as H. change(coding_lt M(zeroM M)(code_numeral M 1))in H.
   rewrite E in H. exact(coding_not_lt_zero M _ H). }
 assert(H1F:code_numeral M 1<>fresh).
 { intro E. rewrite <-E in HOne. apply(proj1(coding_lt_succ_cancel M(zeroM M)(zeroM M)))in HOne.
   exact(coding_not_lt_zero M _ HOne). }
 pose proof(source_zero_transposition_other M fresh b c(code_numeral M 1)HTrans H1Z H1F)as ROne.
 exists ie,iw,iset,ix,ip. split;[exact RE|]. split.
 - exact(source_native_witness_carrier_transposition M phi shifted n fresh b c witness iw BP HCut HF HTrans HW HW').
 - split;[exact(source_subset_closed_carrier_renaming M(zeroM M)subsetclosed fresh iset b c(succM M fresh)(zeroM M)HS HS'
     (source_zero_transposition_zero M fresh b c HTrans))|]. split.
   + apply(proj2(numerical_renaming_member M fresh(zeroM M)xb b c(succM M fresh)(zeroM M)ix HXB)).
     exists(zeroM M),fresh. repeat first[assumption|split].
     * exact(source_zero_transposition_name M fresh b c HTrans).
     * exact(source_zero_transposition_zero M fresh b c HTrans).
   + split.
     * apply(proj2(numerical_renaming_member M(code_numeral M 1)(zeroM M)pb b c(succM M fresh)(zeroM M)ip HPB)).
       exists(code_numeral M 1),fresh. repeat first[assumption|split].
       exact(source_zero_transposition_zero M fresh b c HTrans).
     * split;[exact HRE|]. split;[exact HRW|]. split;[exact HRS|]. split.
       -- exact(source_relativization_atom M domain SFMember(zeroM M)fresh ix(or_introl eq_refl)HIX).
       -- exact(source_relativization_atom M domain SFMember(code_numeral M 1)fresh ip(or_introl eq_refl)HIP).
Qed.
Print Assumptions source_native_relative_premise_graphs.
