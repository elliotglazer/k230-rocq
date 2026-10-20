(** Exact arithmetic maps beneath the An successor's environment and
 previous-environment binders. Formulas and their bounds remain internal. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SourceBounded
 NumericalRenamingMaps NumericalRenaming NumericalSubstitutionMaps SourceRenamingIdentity SourceRenamingDiamond
 SourceShiftSpecialization SourceFiniteCutoffShift SourceCutoffShiftCommutation SourceDnStep SourceEnvFScopedHole.
From FOL.Tennenbaum Require Peano.
Unset Implicit Arguments.
Theorem source_low_parameter_shift_cutoff_two M depth f previous result k:
 source_bounded M f k ->source_low_parameter_shift M(S depth)f previous ->
 source_cutoff_shift M 2 previous result ->source_low_parameter_shift M(S(S depth))f result.
Proof.
 intros BF HR(b&c&n&HM&HS).
 pose proof(source_cutoff_shift_map_renaming M 2 previous result b c n HM HS)as HT.
 assert(HId:numerical_renaming M f(zeroM M)(zeroM M)(zeroM M)(zeroM M)f).
 { apply(numerical_renaming_identity_on_bound M f _ _ _ _ k BF). intros i _. apply source_empty_renaming_lookup. }
 apply(numerical_source_renaming_diamond M f k
  (zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M(S depth))
  (zeroM M)(zeroM M)(zeroM M)(zeroM M) b c n(code_numeral M 1)
  (zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M(S(S depth)))previous f result BF HR HId HT).
 intros i j l m HI HJ HM0 HIdI.
 rewrite(renaming_lookup_functional M _ _ _ _ i l i HIdI(source_empty_renaming_lookup M i)).
 apply(proj1(source_cutoff_shift_map_renaming_lookup M 2 b c n j m HM))in HM0.
 destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)as[->|[q ->]].
 - rewrite(renaming_lookup_functional M _ _ _ _ _ j _ HJ(low_parameter_lookup_zero M(S depth)))in HM0.
   rewrite(substitution_lookup_functional M _ _ _ _ _ m _ HM0(source_cutoff_shift_map_fixed_lookup M 2 b c n HM 0)).
   apply low_parameter_lookup_zero.
 - assert(HNon:succM M q<>zeroM M)by(exact(fun E=>Model.zero_ne_succ M q(eq_sym E))).
   rewrite(renaming_lookup_functional M _ _ _ _ _ j _ HJ(low_parameter_lookup_nonzero M(S depth)(succM M q)HNon))in HM0.
   assert(EJ:addM M(succM M q)(code_numeral M(S depth))=succM M(succM M(addM M q(code_numeral M depth)))).
   { change(addM M(succM M q)(succM M(code_numeral M depth))=succM M(succM M(addM M q(code_numeral M depth)))).
     rewrite Arithmetic.add_comm,Arithmetic.add_succ,Arithmetic.add_comm,Arithmetic.add_succ. reflexivity. }
   rewrite EJ in HM0.
   pose proof(source_cutoff_shift_map_tail_lookup M 2 b c n(addM M q(code_numeral M depth))HM)as HLookup.
   change(substitution_lookup M b c n(code_numeral M 3)(succM M(succM M(addM M q(code_numeral M depth))))
     (succM M(succM M(succM M(addM M q(code_numeral M depth))))))in HLookup.
   rewrite(substitution_lookup_functional M _ _ _ _ _ m _ HM0 HLookup).
   replace(succM M(succM M(succM M(addM M q(code_numeral M depth)))))with(addM M(succM M q)(code_numeral M(S(S depth)))).
   + apply low_parameter_lookup_nonzero. exact HNon.
   + change(addM M(succM M q)(succM M(succM M(code_numeral M depth)))=
      succM M(succM M(succM M(addM M q(code_numeral M depth))))).
     rewrite Arithmetic.add_comm,!Arithmetic.add_succ,Arithmetic.add_comm,Arithmetic.add_succ. reflexivity.
Qed.
Definition environment_rotation_lifts M b c n d e l:=
 renaming_lift M(code_numeral M 1653)(code_numeral M 6)(code_numeral M 3)(zeroM M)b c n /\
 renaming_lift M b c n(zeroM M)d e l.
Lemma environment_rotation_lift_twice M b c n d e l i j:
 environment_rotation_lifts M b c n d e l ->
 renaming_lookup M(code_numeral M 1653)(code_numeral M 6)(code_numeral M 3)(zeroM M)i j ->
 renaming_lookup M d e l(zeroM M)(succM M(succM M i))(succM M(succM M j)).
Proof.
 intros(HL1&HL2)HI.
 apply(proj2(renaming_lift_tail M b c n(zeroM M)d e l(succM M i)(succM M j)HL2)).
 exact(proj2(renaming_lift_tail M _ _ _ _ b c n i j HL1)HI).
Qed.
Lemma environment_rotation_zero M b c n d e l:environment_rotation_lifts M b c n d e l ->
 renaming_lookup M d e l(zeroM M)(zeroM M)(zeroM M).
Proof. intros(H1&H2). exact(proj2(renaming_lift_head M b c n(zeroM M)d e l(zeroM M)H2)eq_refl). Qed.
Lemma environment_rotation_one M b c n d e l:environment_rotation_lifts M b c n d e l ->
 renaming_lookup M d e l(zeroM M)(code_numeral M 1)(code_numeral M 1).
Proof.
 intros(H1&H2). apply(proj2(renaming_lift_tail M b c n(zeroM M)d e l(zeroM M)(zeroM M)H2)).
 exact(proj2(renaming_lift_head M _ _ _ _ b c n(zeroM M)H1)eq_refl).
Qed.
Lemma environment_rotation_two M b c n d e l:environment_rotation_lifts M b c n d e l ->
 renaming_lookup M d e l(zeroM M)(code_numeral M 2)(code_numeral M 3).
Proof. intro H. exact(environment_rotation_lift_twice M b c n d e l(zeroM M)(code_numeral M 1)H(source_dn_rotate_zero M)). Qed.
Lemma environment_rotation_three M b c n d e l:environment_rotation_lifts M b c n d e l ->
 renaming_lookup M d e l(zeroM M)(code_numeral M 3)(code_numeral M 4).
Proof. intro H. exact(environment_rotation_lift_twice M b c n d e l(code_numeral M 1)(code_numeral M 2)H(source_dn_rotate_one M)). Qed.
Lemma environment_rotation_four M b c n d e l:environment_rotation_lifts M b c n d e l ->
 renaming_lookup M d e l(zeroM M)(code_numeral M 4)(code_numeral M 2).
Proof. intro H. exact(environment_rotation_lift_twice M b c n d e l(code_numeral M 2)(zeroM M)H(source_dn_rotate_two M)). Qed.
Lemma environment_rotation_above M b c n d e l i:environment_rotation_lifts M b c n d e l ->
 renaming_lookup M d e l(zeroM M)(source_succ_iter M 5 i)(source_succ_iter M 5 i).
Proof.
 intro H. apply(environment_rotation_lift_twice M b c n d e l(source_succ_iter M 3 i)(source_succ_iter M 3 i)H).
 apply source_dn_rotate_outside. intro HBad.
 change(coding_lt M(succM M(succM M(succM M i)))(succM M(succM M(succM M(zeroM M)))))in HBad.
 exact(coding_not_lt_zero M i(proj1(coding_lt_succ_cancel M i(zeroM M))
  (proj1(coding_lt_succ_cancel M(succM M i)(succM M(zeroM M)))
   (proj1(coding_lt_succ_cancel M(succM M(succM M i))(succM M(succM M(zeroM M))))HBad)))).
Qed.
Theorem source_low_four_rotation_invariant M f deep k b c n d e l:
 source_bounded M f k ->source_low_parameter_shift M 4 f deep ->environment_rotation_lifts M b c n d e l ->
 numerical_renaming M deep d e l(zeroM M)deep.
Proof.
 intros BF HD HL.
 assert(HId:numerical_renaming M f(zeroM M)(zeroM M)(zeroM M)(zeroM M)f).
 { apply(numerical_renaming_identity_on_bound M f _ _ _ _ k BF). intros i _. apply source_empty_renaming_lookup. }
 apply(numerical_source_renaming_diamond M f k
  (zeroM M)(zeroM M)(zeroM M)(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M 4)
  (zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M 4)d e l(zeroM M)f deep deep BF HId HD HD).
 intros i j q v HI HJ HV HQ.
 rewrite(renaming_lookup_functional M _ _ _ _ i j i HJ(source_empty_renaming_lookup M i))in HV.
 assert(E:q=v)by(eapply renaming_lookup_functional;eassumption). subst v.
 destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)as[->|[r ->]].
 - rewrite(renaming_lookup_functional M _ _ _ _ _ q _ HQ(low_parameter_lookup_zero M 4)). exact(environment_rotation_zero M b c n d e l HL).
 - assert(HNon:succM M r<>zeroM M)by(exact(fun E=>Model.zero_ne_succ M r(eq_sym E))).
   rewrite(renaming_lookup_functional M _ _ _ _ _ q _ HQ(low_parameter_lookup_nonzero M 4(succM M r)HNon)).
   replace(addM M(succM M r)(code_numeral M 4))with(source_succ_iter M 5 r).
   + exact(environment_rotation_above M b c n d e l r HL).
   + change(succM M(succM M(succM M(succM M(succM M r))))=addM M(succM M r)(succM M(succM M(succM M(succM M(zeroM M)))))).
     rewrite Arithmetic.add_comm,!Arithmetic.add_succ,Arithmetic.add_zero. reflexivity.
Qed.
Print Assumptions source_low_parameter_shift_cutoff_two.
Print Assumptions source_low_four_rotation_invariant.
