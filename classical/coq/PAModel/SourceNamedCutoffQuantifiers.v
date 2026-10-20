(** Exact link between a canonical de Bruijn binder and named closure.
 The source formula and its free-index bound are arbitrary internal codes. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 SourceFiniteCutoffShift SourceCutoffShiftCommutation SourceRepresentativeRenaming SourceRepresentativeQuantifier
 NumericalRenamingMaps NumericalRenaming NumericalSubstitutionMaps RawBinderRenaming SourceNamedQuantifierRules.
From FOL.Tennenbaum Require Peano.
Unset Implicit Arguments.
Lemma source_cutoff_one_raw_zero M b c n:
 source_cutoff_shift_map M 1 b c n ->forall i v,
 renaming_lookup M b c n(code_numeral M 1)i v <->raw_binder_index M(zeroM M)i v.
Proof.
 intros HM i v. rewrite(source_cutoff_shift_map_renaming_lookup M 1 b c n i v HM).
 destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)
   (fun ax H rho=>axioms M ax rho H)i)as[->|[j ->]].
 - pose proof(source_cutoff_shift_map_fixed_lookup M 1 b c n HM 0)as HZero.
   change(substitution_lookup M b c n(code_numeral M 2)(zeroM M)(zeroM M))in HZero.
   split.
   + intro HV. left. split;[reflexivity|]. eapply substitution_lookup_functional;eassumption.
   + intros[[ _ ->]|[HN _]];[exact HZero|contradiction].
 - pose proof(source_cutoff_shift_map_tail_lookup M 1 b c n j HM)as HTail.
   change(substitution_lookup M b c n(code_numeral M 2)(succM M j)(succM M(succM M j)))in HTail.
   split.
   + intro HV. right. split;[intro E;exact(Model.zero_ne_succ M j(eq_sym E))|].
     eapply substitution_lookup_functional;eassumption.
   + intros[[E _]|[_ ->]];[exfalso;exact(Model.zero_ne_succ M j(eq_sym E))|exact HTail].
Qed.
Theorem source_named_zero_quantifier_cutoff M(universal:bool)f body result:
 source_cutoff_shift M 1 f body ->sf_relation M(if universal then SFAll else SFEx)body(zeroM M)result ->
 source_named_quantifier M universal(zeroM M)f result.
Proof.
 intros(b&c&n&HM&HR)HQ.
 destruct(raw_binder_renaming_total M(zeroM M))as(rb&rc&HRaw).
 exists rb,rc,body. split;[exact HRaw|]. split;[|exact HQ].
 pose proof(source_cutoff_shift_map_renaming M 1 f body b c n HM HR)as HMap.
 assert(HE:renaming_equivalent M b c n rb rc(code_numeral M 1)(code_numeral M 1)).
 { intros i v. rewrite(source_cutoff_one_raw_zero M b c n HM i v),(HRaw i v). reflexivity. }
 exact(proj1(numerical_renaming_extensional M f b c n rb rc(code_numeral M 1)(code_numeral M 1)body HE)HMap).
Qed.
Theorem source_named_fresh_quantifier_cutoff M(universal:bool)f renamed name k body result:
 source_bounded M f k ->~coding_lt M name k ->source_representative_renaming M name f renamed ->
 source_cutoff_shift M 1 f body ->sf_relation M(if universal then SFAll else SFEx)body(zeroM M)result ->
 source_named_quantifier M universal name renamed result.
Proof.
 intros BF HFresh HName HCut HQ.
 destruct(source_named_quantifier_total M universal name renamed)as(other&HOther).
 pose proof(source_named_zero_quantifier_cutoff M(universal:bool)f body result HCut HQ)as HZero.
 rewrite<-(source_representative_quantifier_normalization M universal f renamed name k other result
  BF HFresh HName HOther HZero). exact HOther.
Qed.
Print Assumptions source_named_zero_quantifier_cutoff.
Print Assumptions source_named_fresh_quantifier_cutoff.
