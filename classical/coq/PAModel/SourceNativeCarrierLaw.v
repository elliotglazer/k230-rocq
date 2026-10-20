(** The complete raw carrier inference is an actual pure source theorem.
    The five original premises occur as antecedents, not proof assumptions. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
  SourceBounded SourceFiniteCutoffShift SourceNativeKRecipes SourceUpperTraceProfile SourceUpperTraceFrame
  SourceUpperWitnessRecipes SourceZeroTransposition SourceUpperPremiseBounds SourceFivePremiseLaw
  SourceNativeUpperBoundImages NumericalRenaming NumericalRenamingMaps SourceRenamingWellformedness
  SourceRenamingBounds NumericalContexts NumericalSourceFull.
Unset Implicit Arguments.

Definition source_native_carrier_law_graph M fresh b c exprofile witness subsetclosed xb pb target law :=
  exists ie iw iset ix ip l5 l4 l3 l2,
    numerical_renaming M exprofile b c (succM M fresh)(zeroM M) ie /\
    numerical_renaming M witness b c (succM M fresh)(zeroM M) iw /\
    numerical_renaming M subsetclosed b c (succM M fresh)(zeroM M) iset /\
    numerical_renaming M xb b c (succM M fresh)(zeroM M) ix /\
    numerical_renaming M pb b c (succM M fresh)(zeroM M) ip /\
    sf_relation M SFImpl ip target l5 /\sf_relation M SFImpl ix l5 l4 /\
    sf_relation M SFImpl iset l4 l3 /\sf_relation M SFImpl iw l3 l2 /\sf_relation M SFImpl ie l2 law.

Lemma source_renaming_finite_bound M f k b c n delta g :
  source_bounded M f k ->numerical_renaming M f b c n delta g ->exists l,source_bounded M g l.
Proof.
  intros HF HR. destruct (source_renaming_range_bound M b c n delta k) as [l HL].
  exists l. exact (numerical_renaming_preserves_bound M f b c n delta g k l HF HR HL).
Qed.

Theorem source_full_native_carrier_law M phi phi' n fresh b c
    profile exprofile witness subsetclosed xb pb target law :
  source_bounded M phi (succM M (succM M n)) ->source_cutoff_shift M 2 phi phi' ->
  coding_lt M (succM M (succM M n)) fresh ->source_zero_transposition M fresh b c ->
  source_upper_trace_profile M phi' profile ->sf_relation M SFEx profile (zeroM M) exprofile ->
  source_upper_witness_closed_recipe M phi' (code_numeral M 1)(zeroM M) witness ->
  source_subset_closed_graph M (zeroM M) subsetclosed ->
  sf_relation M SFMember fresh (zeroM M) xb ->sf_relation M SFMember (code_numeral M 1)(zeroM M) pb ->
  source_upper_conclusion_recipe M phi target ->
  source_native_carrier_law_graph M fresh b c exprofile witness subsetclosed xb pb target law ->
  source_full_prv M (zeroM M)(zeroM M)(zeroM M) law.
Proof.
  intros HP HS HF HM HProfile HEx HW HSC HXB HPB HT
    (ie&iw&iset&ix&ip&l5&l4&l3&l2&REx&RW&RS&RX&RP&H5&H4&H3&H2&H1).
  pose proof (source_cutoff_shift_bounded M 2 phi phi' n HP HS) as HP'.
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
  destruct (source_renaming_finite_bound M exprofile _ b c (succM M fresh)(zeroM M) ie BEx REx) as [ke BE].
  destruct (source_renaming_finite_bound M witness _ b c (succM M fresh)(zeroM M) iw BW RW) as [kw BIW].
  destruct (source_renaming_finite_bound M subsetclosed _ b c (succM M fresh)(zeroM M) iset BS RS) as [ks BIS].
  destruct (source_renaming_finite_bound M xb _ b c (succM M fresh)(zeroM M) ix BX RX) as [kx BIX].
  destruct (source_renaming_finite_bound M pb _ b c (succM M fresh)(zeroM M) ip BP RP) as [kp BIP].
  apply (source_full_five_premise_law M ie iw iset ix ip target l5 l4 l3 l2 law ke kw ks kx kp
    BE BIW BIS BIX BIP H5 H4 H3 H2 H1).
  intros cb cc cn PE PW PS PX PP.
  exact (source_full_native_upper_from_bound_images M cb cc cn phi phi' n fresh b c
    profile exprofile witness subsetclosed xb pb ie iw iset ix ip target
    HP HS HF HM HProfile HEx HW HSC HXB HPB REx RW RS RX RP HT PE PW PS PX PP).
Qed.

Theorem source_native_carrier_law_total M phi phi' n fresh b c
    profile exprofile witness subsetclosed xb pb target :
  source_bounded M phi (succM M (succM M n)) ->source_cutoff_shift M 2 phi phi' ->
  coding_lt M (succM M (succM M n)) fresh ->source_zero_transposition M fresh b c ->
  source_upper_trace_profile M phi' profile ->sf_relation M SFEx profile (zeroM M) exprofile ->
  source_upper_witness_closed_recipe M phi' (code_numeral M 1)(zeroM M) witness ->
  source_subset_closed_graph M (zeroM M) subsetclosed ->
  sf_relation M SFMember fresh (zeroM M) xb ->sf_relation M SFMember (code_numeral M 1)(zeroM M) pb ->
  source_upper_conclusion_recipe M phi target ->
  exists law,source_native_carrier_law_graph M fresh b c exprofile witness subsetclosed xb pb target law /\
    source_full_prv M (zeroM M)(zeroM M)(zeroM M) law.
Proof.
  intros HP HS HF HM HProfile HEx HW HSC HXB HPB HT.
  destruct (numerical_renaming_total M exprofile b c (succM M fresh)(zeroM M)) as [ie RE].
  destruct (numerical_renaming_total M witness b c (succM M fresh)(zeroM M)) as [iw RW].
  destruct (numerical_renaming_total M subsetclosed b c (succM M fresh)(zeroM M)) as [iset RS].
  destruct (numerical_renaming_total M xb b c (succM M fresh)(zeroM M)) as [ix RX].
  destruct (numerical_renaming_total M pb b c (succM M fresh)(zeroM M)) as [ip RP].
  destruct (sf_relation_total M SFImpl ip target) as [l5 H5].
  destruct (sf_relation_total M SFImpl ix l5) as [l4 H4].
  destruct (sf_relation_total M SFImpl iset l4) as [l3 H3].
  destruct (sf_relation_total M SFImpl iw l3) as [l2 H2].
  destruct (sf_relation_total M SFImpl ie l2) as [law H1].
  assert (HG:source_native_carrier_law_graph M fresh b c exprofile witness subsetclosed xb pb target law).
  { exists ie,iw,iset,ix,ip,l5,l4,l3,l2. repeat first [assumption|split]. }
  exists law. split;[exact HG|].
  exact (source_full_native_carrier_law M phi phi' n fresh b c profile exprofile witness subsetclosed xb pb target law
    HP HS HF HM HProfile HEx HW HSC HXB HPB HT HG).
Qed.

Print Assumptions source_full_native_carrier_law.
Print Assumptions source_native_carrier_law_total.
