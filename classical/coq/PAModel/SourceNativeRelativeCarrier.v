(** The actual carrier inference transported through literal source
    relativization. All five hypotheses are concrete syntax images. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceBounded SourceFiniteCutoffShift SourceNativeKRecipes SourceUpperTraceProfile
  SourceUpperTraceFrame SourceUpperWitnessRecipes SourceZeroTransposition
  SourceNativeCarrierLaw SourcePureRelativeRule SourceDerivedRules
  NumericalRenaming NumericalContexts NumericalInstantiation NumericalSourceFull
  SourceRelativization SourceContextTransport.
Unset Implicit Arguments.

Definition source_native_carrier_relative_premises M domain fresh b c
    exprofile witness subsetclosed xb pb re rw rs rx rp :=
  exists ie iw iset ix ip,
    numerical_renaming M exprofile b c (succM M fresh)(zeroM M) ie /\
    numerical_renaming M witness b c (succM M fresh)(zeroM M) iw /\
    numerical_renaming M subsetclosed b c (succM M fresh)(zeroM M) iset /\
    numerical_renaming M xb b c (succM M fresh)(zeroM M) ix /\
    numerical_renaming M pb b c (succM M fresh)(zeroM M) ip /\
    source_relativization M domain ie re /\source_relativization M domain iw rw /\
    source_relativization M domain iset rs /\source_relativization M domain ix rx /\
    source_relativization M domain ip rp.

Theorem source_native_carrier_relative_premises_total M domain fresh b c exprofile witness subsetclosed xb pb :
  exists re rw rs rx rp,
    source_native_carrier_relative_premises M domain fresh b c exprofile witness subsetclosed xb pb re rw rs rx rp.
Proof.
  destruct (numerical_renaming_total M exprofile b c (succM M fresh)(zeroM M)) as [ie RE].
  destruct (numerical_renaming_total M witness b c (succM M fresh)(zeroM M)) as [iw RW].
  destruct (numerical_renaming_total M subsetclosed b c (succM M fresh)(zeroM M)) as [iset RS].
  destruct (numerical_renaming_total M xb b c (succM M fresh)(zeroM M)) as [ix RX].
  destruct (numerical_renaming_total M pb b c (succM M fresh)(zeroM M)) as [ip RP].
  destruct (source_relativization_total M domain ie) as [re HE].
  destruct (source_relativization_total M domain iw) as [rw HW].
  destruct (source_relativization_total M domain iset) as [rs HS].
  destruct (source_relativization_total M domain ix) as [rx HX].
  destruct (source_relativization_total M domain ip) as [rp HP].
  exists re,rw,rs,rx,rp,ie,iw,iset,ix,ip. repeat first [assumption|split].
Qed.

Theorem source_full_native_relative_carrier M domain phi phi' n fresh b c
    profile exprofile witness subsetclosed xb pb target relative re rw rs rx rp :
  source_bounded M domain (code_numeral M 1) ->
  source_bounded M phi (succM M (succM M n)) ->source_cutoff_shift M 2 phi phi' ->
  coding_lt M (succM M (succM M n)) fresh ->source_zero_transposition M fresh b c ->
  source_upper_trace_profile M phi' profile ->sf_relation M SFEx profile (zeroM M) exprofile ->
  source_upper_witness_closed_recipe M phi' (code_numeral M 1)(zeroM M) witness ->
  source_subset_closed_graph M (zeroM M) subsetclosed ->
  sf_relation M SFMember fresh (zeroM M) xb ->sf_relation M SFMember (code_numeral M 1)(zeroM M) pb ->
  source_upper_conclusion_recipe M phi target ->source_relativization M domain target relative ->
  source_native_carrier_relative_premises M domain fresh b c exprofile witness subsetclosed xb pb re rw rs rx rp ->
  exists bound,forall k db dc dn,
    coding_lt M bound (succM M k) ->source_context_finite_bound M db dc dn ->
    (forall i di,coding_lt M i k ->numerical_instantiation M domain i di ->source_full_prv M db dc dn di) ->
    source_full_prv M db dc dn re ->source_full_prv M db dc dn rw ->
    source_full_prv M db dc dn rs ->source_full_prv M db dc dn rx ->source_full_prv M db dc dn rp ->
    source_full_prv M db dc dn relative.
Proof.
  intros HD HP HS HF HM HProfile HEx HW HSC HXB HPB HT HRel
    (ie&iw&iset&ix&ip&RE&RW&RS&RX&RP&HRE&HRW&HRS&HRX&HRP).
  destruct (sf_relation_total M SFImpl ip target) as [l5 H5].
  destruct (sf_relation_total M SFImpl ix l5) as [l4 H4].
  destruct (sf_relation_total M SFImpl iset l4) as [l3 H3].
  destruct (sf_relation_total M SFImpl iw l3) as [l2 H2].
  destruct (sf_relation_total M SFImpl ie l2) as [law H1].
  assert (HLaw:source_native_carrier_law_graph M fresh b c exprofile witness subsetclosed xb pb target law).
  { exists ie,iw,iset,ix,ip,l5,l4,l3,l2. repeat first [assumption|split]. }
  pose proof (source_full_native_carrier_law M phi phi' n fresh b c profile exprofile witness subsetclosed xb pb
    target law HP HS HF HM HProfile HEx HW HSC HXB HPB HT HLaw) as PLaw.
  destruct (sf_relation_total M SFImpl rp relative) as [r5 G5].
  destruct (sf_relation_total M SFImpl rx r5) as [r4 G4].
  destruct (sf_relation_total M SFImpl rs r4) as [r3 G3].
  destruct (sf_relation_total M SFImpl rw r3) as [r2 G2].
  destruct (sf_relation_total M SFImpl re r2) as [rlaw G1].
  assert (HR5:source_relativization M domain l5 r5).
  { exact (source_relativization_binary M domain SFImpl ip target l5 rp relative r5
      (or_intror (or_intror eq_refl)) H5 HRP HRel G5). }
  assert (HR4:source_relativization M domain l4 r4).
  { exact (source_relativization_binary M domain SFImpl ix l5 l4 rx r5 r4
      (or_intror (or_intror eq_refl)) H4 HRX HR5 G4). }
  assert (HR3:source_relativization M domain l3 r3).
  { exact (source_relativization_binary M domain SFImpl iset l4 l3 rs r4 r3
      (or_intror (or_intror eq_refl)) H3 HRS HR4 G3). }
  assert (HR2:source_relativization M domain l2 r2).
  { exact (source_relativization_binary M domain SFImpl iw l3 l2 rw r3 r2
      (or_intror (or_intror eq_refl)) H2 HRW HR3 G2). }
  assert (HR1:source_relativization M domain law rlaw).
  { exact (source_relativization_binary M domain SFImpl ie l2 law re r2 rlaw
      (or_intror (or_intror eq_refl)) H1 HRE HR2 G1). }
  destruct (source_pure_relative_rule M domain law HD PLaw) as [bound HApply].
  exists bound. intros k db dc dn HB HC HDom PE PW PS PX PP.
  pose proof (HApply k db dc dn rlaw HB HC HDom HR1) as PRLaw.
  pose proof (source_full_modus_ponens M db dc dn re r2 rlaw G1 PRLaw PE) as P2.
  pose proof (source_full_modus_ponens M db dc dn rw r3 r2 G2 P2 PW) as P3.
  pose proof (source_full_modus_ponens M db dc dn rs r4 r3 G3 P3 PS) as P4.
  pose proof (source_full_modus_ponens M db dc dn rx r5 r4 G4 P4 PX) as P5.
  exact (source_full_modus_ponens M db dc dn rp relative r5 G5 P5 PP).
Qed.

Print Assumptions source_native_carrier_relative_premises_total.
Print Assumptions source_full_native_relative_carrier.
