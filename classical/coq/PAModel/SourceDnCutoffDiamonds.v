(** Exact map square between the Dn rotation and two external ordinal names. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions NumericalProofs SetFormulaCodes
  NumericalEnvironments NumericalRenamingMaps NumericalRenaming NumericalSubstitutionMaps NumericalSubstitution
  SourceNumeralLift SourceDnStep SourceDnRotation4 SourceBounded SourceRenamingSquare
  SourceFiniteCutoffShift SourceCutoffShiftCommutation SourceQuantifierRules RenamingSubstitution.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Lemma source_dn_rotate_fixed M i : (i<3)%nat ->
  renaming_lookup M(code_numeral M 1653)(code_numeral M 6)(code_numeral M 3)(zeroM M)
    (code_numeral M i)(code_numeral M(match i with 0=>1|1=>2|2=>0|_=>i end)).
Proof.
  intro HI. destruct i as [|[|[|i]]];try lia;
    [apply source_dn_rotate_zero|apply source_dn_rotate_one|apply source_dn_rotate_two].
Qed.

Theorem source_dn_rotate_cutoff_square M depth f fs fr out k : (depth<2)%nat ->
  source_bounded M f k ->source_cutoff_shift M depth f fs ->
  numerical_renaming M f(code_numeral M 1653)(code_numeral M 6)(code_numeral M 3)(zeroM M) fr ->
  source_dn_rotate4 M fs out ->source_cutoff_shift M(S depth) fr out.
Proof.
  intros HD HF (sb&sc&sn&HSM&HS) HR HT.
  destruct(source_cutoff_shift_map_total M(S depth)) as (ub&uc&un&HUM).
  exists ub,uc,un. split;[exact HUM|].
  apply(numerical_source_renaming_square M f k sb sc sn(code_numeral M(S depth))
    (code_numeral M 1653)(code_numeral M 6)(code_numeral M 3)(zeroM M)
    (code_numeral M 5475)(code_numeral M 6)(code_numeral M 4)(zeroM M)
    ub uc un(code_numeral M(S(S depth))) fs fr out HF HS HR HT).
  intros i j l m HI HSI HTJ HRI.
  destruct(environment_lt_cases M i(code_numeral M 3)) as [HSmall|HLarge].
  - destruct(source_numeral_initial_segment M 3 i HSmall) as (v&HV&->).
    assert(EJ:j=code_numeral M(sf_index(source_shift_sigma depth v))).
    { eapply substitution_lookup_functional;[exact HSI|exact(source_cutoff_shift_map_fixed_lookup M depth sb sc sn HSM v)]. }
    assert(EL:l=code_numeral M(match v with 0=>1|1=>2|2=>0|_=>v end)).
    { eapply renaming_lookup_functional;[exact HRI|apply source_dn_rotate_fixed;exact HV]. }
    subst j l.
    destruct depth as [|[|depth]];try lia;destruct v as [|[|[|v]]];try lia.
    + assert(EM:m=code_numeral M 2) by (eapply renaming_lookup_functional;[exact HTJ|exact(source_dn_rotate4_fixed M 1 ltac:(lia))]).
      subst m. exact(source_cutoff_shift_map_fixed_lookup M 1 ub uc un HUM 1).
    + assert(EM:m=code_numeral M 3) by (eapply renaming_lookup_functional;[exact HTJ|exact(source_dn_rotate4_fixed M 2 ltac:(lia))]).
      subst m. exact(source_cutoff_shift_map_fixed_lookup M 1 ub uc un HUM 2).
    + assert(EM:m=zeroM M) by (eapply renaming_lookup_functional;[exact HTJ|exact(source_dn_rotate4_fixed M 3 ltac:(lia))]).
      subst m. exact(source_cutoff_shift_map_fixed_lookup M 1 ub uc un HUM 0).
    + assert(EM:m=code_numeral M 1) by (eapply renaming_lookup_functional;[exact HTJ|exact(source_dn_rotate4_fixed M 0 ltac:(lia))]).
      subst m. exact(source_cutoff_shift_map_fixed_lookup M 2 ub uc un HUM 1).
    + assert(EM:m=code_numeral M 3) by (eapply renaming_lookup_functional;[exact HTJ|exact(source_dn_rotate4_fixed M 2 ltac:(lia))]).
      subst m. exact(source_cutoff_shift_map_fixed_lookup M 2 ub uc un HUM 2).
    + assert(EM:m=zeroM M) by (eapply renaming_lookup_functional;[exact HTJ|exact(source_dn_rotate4_fixed M 3 ltac:(lia))]).
      subst m. exact(source_cutoff_shift_map_fixed_lookup M 2 ub uc un HUM 0).
  - destruct(@Peano.zero_or_succ (carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H) i) as [E|[a E]].
    { subst i. contradiction(HLarge(coding_zero_lt_succ M(code_numeral M 2))). }
    subst i. destruct(@Peano.zero_or_succ (carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H) a) as [E|[b E]].
    { subst a. exfalso. apply HLarge. apply coding_lt_succ_cancel,coding_zero_lt_succ. }
    subst a. destruct(@Peano.zero_or_succ (carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H) b) as [E|[z E]].
    { subst b. exfalso. apply HLarge. apply coding_lt_succ_cancel,coding_lt_succ_cancel,coding_zero_lt_succ. }
    subst b.
    assert(EL:l=succM M(succM M(succM M z))).
    { eapply renaming_lookup_functional;[exact HRI|apply source_dn_rotate_outside;exact HLarge]. }
    subst l.
    assert(EJ:j=succM M(succM M(succM M(succM M z)))).
    { eapply substitution_lookup_functional;[exact HSI|].
      destruct depth as [|[|depth]];try lia.
      - exact(source_cutoff_shift_map_tail_lookup M 0 sb sc sn(succM M(succM M(succM M z))) HSM).
      - exact(source_cutoff_shift_map_tail_lookup M 1 sb sc sn(succM M(succM M z)) HSM). }
    subst j.
    assert(EM:m=succM M(succM M(succM M(succM M z)))).
    { eapply renaming_lookup_functional;[exact HTJ|apply source_dn_rotate4_outside].
      intro HX. apply (proj1(coding_lt_succ_cancel M _ _)) in HX. apply (proj1(coding_lt_succ_cancel M _ _)) in HX. apply (proj1(coding_lt_succ_cancel M _ _)) in HX. apply (proj1(coding_lt_succ_cancel M _ _)) in HX. exact(coding_not_lt_zero M z HX). }
    subst m. destruct depth as [|[|depth]];try lia.
    + exact(source_cutoff_shift_map_tail_lookup M 1 ub uc un(succM M(succM M z)) HUM).
    + exact(source_cutoff_shift_map_tail_lookup M 2 ub uc un(succM M z) HUM).
Qed.

Theorem source_formula_shift_cutoff_zero M f g :
  source_formula_shift M f g <->source_cutoff_shift M 0 f g.
Proof.
  split.
  - intro HR. exists(zeroM M),(zeroM M),(zeroM M). split;[repeat split;reflexivity|].
    pose proof(proj1(numerical_renaming_substitution M f(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1) g) HR) as HS.
    rewrite coding_add_zero in HS. exact HS.
  - intros(b&c&n&[-> [-> ->]]&HS).
    apply(proj2(numerical_renaming_substitution M f(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1) g)).
    rewrite coding_add_zero. exact HS.
Qed.

Print Assumptions source_dn_rotate_cutoff_square.
Print Assumptions source_formula_shift_cutoff_zero.
