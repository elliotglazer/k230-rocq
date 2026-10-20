(** Moving only the representative does not change the assignment guard or
    the shifted source matrix. These are arithmetic map calculations, not
    a freshness assumption on an arbitrary formula. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions NumericalProofs
 NumericalEnvironments NumericalSubstitutionMaps NumericalRenamingMaps NumericalRenaming SourceBounded SourceRenamingIdentity
 SourceRenamingDiamond SourceFiniteCutoffShift SourceCutoffShiftCommutation SourceRepresentativeRenaming.
From FOL.Tennenbaum Require Peano.
Unset Implicit Arguments.

Lemma representative_cutoff_one_lookup_not_one M sb sc sn i j :
 source_cutoff_shift_map M 1 sb sc sn ->
 renaming_lookup M sb sc sn (code_numeral M 1) i j ->j<>code_numeral M 1.
Proof.
 intros HM HJ. apply(proj1(source_cutoff_shift_map_renaming_lookup M 1 sb sc sn i j HM))in HJ.
 destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)
   (fun ax H rho=>axioms M ax rho H) i)as[E|[l E]];subst i.
 - assert(E:j=zeroM M)by(eapply substitution_lookup_functional;[exact HJ|exact(source_cutoff_shift_map_fixed_lookup M 1 sb sc sn HM 0)]).
   subst j. exact(Model.zero_ne_succ M(zeroM M)).
 - assert(E:j=succM M(succM M l))by(eapply substitution_lookup_functional;[exact HJ|exact(source_cutoff_shift_map_tail_lookup M 1 sb sc sn l HM)]).
   subst j. intro E. apply(Model.succ_injective M)in E.
   exact(Model.zero_ne_succ M l(eq_sym E)).
Qed.

Theorem source_representative_lift_fixes_cutoff_one M f g k r b c n :
 source_bounded M f k ->source_cutoff_shift M 1 f g ->
 renaming_lift M r r(code_numeral M 1)(zeroM M) b c n ->
 numerical_renaming M g b c n(zeroM M) g.
Proof.
 intros HF(sb&sc&sn&HM&HG) HL.
 pose proof(source_cutoff_shift_map_renaming M 1 f g sb sc sn HM HG)as HR.
 assert(HI:numerical_renaming M f(zeroM M)(zeroM M)(zeroM M)(zeroM M) f).
 { apply(numerical_renaming_identity_on_bound M f _ _ _ _ k HF).
   intros i _. right. split;[apply coding_not_lt_zero|symmetry;apply coding_add_zero_r]. }
 apply(numerical_source_renaming_diamond M f k
   (zeroM M)(zeroM M)(zeroM M)(zeroM M)
   sb sc sn(code_numeral M 1) sb sc sn(code_numeral M 1)
   b c n(zeroM M) f g g HF HI HR HR).
 intros i j l m _ HJ HM' HL'.
 assert(EJ:j=i).
 { apply(renaming_lookup_outside M(zeroM M)(zeroM M)(zeroM M)(zeroM M) i j(coding_not_lt_zero M i))in HJ.
   now rewrite coding_add_zero_r in HJ. }
 subst j. assert(E:m=l)by(eapply renaming_lookup_functional;eassumption). subst m.
 apply(representative_lift_fixed M r b c n l HL).
 exact(representative_cutoff_one_lookup_not_one M sb sc sn i l HM HL').
Qed.

Theorem source_representative_lift_fixes_shift_three M f g k r b c n :
 source_bounded M f k ->
 numerical_renaming M f(zeroM M)(zeroM M)(zeroM M)(code_numeral M 3) g ->
 renaming_lift M r r(code_numeral M 1)(zeroM M) b c n ->
 numerical_renaming M g b c n(zeroM M) g.
Proof.
 intros HF HG HL.
 assert(HI:numerical_renaming M f(zeroM M)(zeroM M)(zeroM M)(zeroM M) f).
 { apply(numerical_renaming_identity_on_bound M f _ _ _ _ k HF).
   intros i _. right. split;[apply coding_not_lt_zero|symmetry;apply coding_add_zero_r]. }
 apply(numerical_source_renaming_diamond M f k
   (zeroM M)(zeroM M)(zeroM M)(zeroM M)
   (zeroM M)(zeroM M)(zeroM M)(code_numeral M 3)
   (zeroM M)(zeroM M)(zeroM M)(code_numeral M 3)
   b c n(zeroM M) f g g HF HI HG HG).
 intros i j l m _ HJ HM HL'.
 assert(EJ:j=i).
 { apply(renaming_lookup_outside M(zeroM M)(zeroM M)(zeroM M)(zeroM M) i j(coding_not_lt_zero M i))in HJ.
   now rewrite coding_add_zero_r in HJ. }
 subst j. assert(E:m=l)by(eapply renaming_lookup_functional;eassumption). subst m.
 apply(representative_lift_fixed M r b c n l HL).
 apply(renaming_lookup_outside M(zeroM M)(zeroM M)(zeroM M)(code_numeral M 3) i l(coding_not_lt_zero M i))in HL'.
 subst l. rewrite Arithmetic.add_comm. change(addM M(succM M(succM M(succM M(zeroM M)))) i<>succM M(zeroM M)). rewrite !Arithmetic.add_succ,Arithmetic.add_zero.
 intro E. apply(Model.succ_injective M)in E. exact(Model.zero_ne_succ M(succM M i)(eq_sym E)).
Qed.
Print Assumptions source_representative_lift_fixes_cutoff_one.
Print Assumptions source_representative_lift_fixes_shift_three.




