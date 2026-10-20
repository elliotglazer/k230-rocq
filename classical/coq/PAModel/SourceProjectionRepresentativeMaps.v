(** Exact representative maps beneath the three finite projection binders.
    Child matrices and old environments are fixed for proved syntactic reasons. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SourceBounded
 NumericalRenamingMaps NumericalRenaming SourceRepresentativeRenaming SourceRenamingIdentity SourceRenamingDiamond SourceShiftSpecialization
 SourceEnvFScopedHole SourceQuantifierMatrixScopes SourceSetRelativization SourceSetRelativizationRenaming SourceSetRelativizationFunctionality
 SourceNamedFiniteCalibration.
From FOL.Tennenbaum Require Peano.
Unset Implicit Arguments.
Definition projection_representative_lifts M r b c n d e l u v m:=
 renaming_lift M r r(code_numeral M 1)(zeroM M)b c n /\renaming_lift M b c n(zeroM M)d e l /\
 renaming_lift M d e l(zeroM M)u v m.
Lemma projection_representative_two_fixed M r b c n d e l i:
 renaming_lift M r r(code_numeral M 1)(zeroM M)b c n ->renaming_lift M b c n(zeroM M)d e l ->
 i<>code_numeral M 2 ->renaming_lookup M d e l(zeroM M)i i.
Proof.
 intros H1 H2 HI. destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)as[->|[q ->]].
 - exact(proj2(renaming_lift_head M _ _ _ _ d e l(zeroM M)H2)eq_refl).
 - apply(proj2(renaming_lift_tail M _ _ _ _ d e l q q H2)).
   apply(representative_lift_fixed M r b c n q H1). intro E. apply HI. now rewrite E.
Qed.
Lemma projection_representative_three_fixed M r b c n d e l u v m i:
 projection_representative_lifts M r b c n d e l u v m ->i<>code_numeral M 3 ->
 renaming_lookup M u v m(zeroM M)i i.
Proof.
 intros(H1&H2&H3)HI. destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)as[->|[q ->]].
 - exact(proj2(renaming_lift_head M _ _ _ _ u v m(zeroM M)H3)eq_refl).
 - apply(proj2(renaming_lift_tail M _ _ _ _ u v m q q H3)).
   apply(projection_representative_two_fixed M r b c n d e l q H1 H2). intro E. apply HI. now rewrite E.
Qed.
Lemma projection_representative_two_changed M r b c n d e l:
 renaming_lift M r r(code_numeral M 1)(zeroM M)b c n ->renaming_lift M b c n(zeroM M)d e l ->
 renaming_lookup M d e l(zeroM M)(code_numeral M 2)(succM M(succM M r)).
Proof.
 intros H1 H2. apply(proj2(renaming_lift_tail M _ _ _ _ d e l(code_numeral M 1)(succM M r)H2)).
 exact(representative_lift_one M r b c n H1).
Qed.
Theorem projection_representative_fixes_environment M f deep k r b c n d e l u v m:
 source_bounded M f k ->source_low_parameter_shift M 3 f deep ->
 projection_representative_lifts M r b c n d e l u v m ->numerical_renaming M deep u v m(zeroM M)deep.
Proof.
 intros BF HD HL.
 assert(HId:numerical_renaming M f(zeroM M)(zeroM M)(zeroM M)(zeroM M)f).
 { apply(numerical_renaming_identity_on_bound M f _ _ _ _ k BF). intros i _. apply source_empty_renaming_lookup. }
 apply(numerical_source_renaming_diamond M f k
  (zeroM M)(zeroM M)(zeroM M)(zeroM M)
  (zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M 3)
  (zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M 3)u v m(zeroM M)f deep deep BF HId HD HD).
 intros i j a z HI HJ HZ HA.
 rewrite(renaming_lookup_functional M _ _ _ _ i j i HJ(source_empty_renaming_lookup M i))in HZ.
 assert(E:z=a)by(eapply renaming_lookup_functional;eassumption). subst z.
 apply(projection_representative_three_fixed M r b c n d e l u v m a HL).
 destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)as[->|[q ->]].
 - rewrite(renaming_lookup_functional M _ _ _ _ _ a _ HA(low_parameter_lookup_zero M 3)).
   exact(source_fixed_numeral_neq M 0 3 ltac:(discriminate)).
 - assert(HN:succM M q<>zeroM M)by(exact(fun E=>Model.zero_ne_succ M q(eq_sym E))).
   rewrite(renaming_lookup_functional M _ _ _ _ _ a _ HA(low_parameter_lookup_nonzero M 3 _ HN)).
   rewrite Arithmetic.add_comm. cbn[code_numeral]. rewrite!Arithmetic.add_succ,Arithmetic.add_zero.
   intro E. do 3 apply(Model.succ_injective M)in E. exact(Model.zero_ne_succ M q(eq_sym E)).
Qed.
Theorem projection_representative_fixes_child_matrix M f child k r b c n d e l:
 source_bounded M f k ->source_quantifier_matrix M(code_numeral M 1)f child ->
 renaming_lift M r r(code_numeral M 1)(zeroM M)b c n ->renaming_lift M b c n(zeroM M)d e l ->
 numerical_renaming M child d e l(zeroM M)child.
Proof.
 intros BF HC H1 H2.
 assert(HId:numerical_renaming M f(zeroM M)(zeroM M)(zeroM M)(zeroM M)f).
 { apply(numerical_renaming_identity_on_bound M f _ _ _ _ k BF). intros i _. apply source_empty_renaming_lookup. }
 apply(numerical_source_renaming_diamond M f k
  (zeroM M)(zeroM M)(zeroM M)(zeroM M)
  (code_numeral M 1)(code_numeral M 1)(code_numeral M 1)(code_numeral M 3)
  (code_numeral M 1)(code_numeral M 1)(code_numeral M 1)(code_numeral M 3)d e l(zeroM M)f child child BF HId HC HC).
 intros i j a z HI HJ HZ HA.
 rewrite(renaming_lookup_functional M _ _ _ _ i j i HJ(source_empty_renaming_lookup M i))in HZ.
 assert(E:z=a)by(eapply renaming_lookup_functional;eassumption). subst z.
 apply(projection_representative_two_fixed M r b c n d e l a H1 H2).
 destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)as[->|[q ->]].
 - rewrite(renaming_lookup_functional M _ _ _ _ _ a _ HA(source_one_role_zero_lookup M(code_numeral M 1)(code_numeral M 3))).
   exact(source_fixed_numeral_neq M 1 2 ltac:(discriminate)).
 - assert(HN:succM M q<>zeroM M)by(exact(fun E=>Model.zero_ne_succ M q(eq_sym E))).
   rewrite(renaming_lookup_functional M _ _ _ _ _ a _ HA(source_one_role_positive_lookup M(code_numeral M 1)(code_numeral M 3)_ HN)).
   rewrite Arithmetic.add_comm. cbn[code_numeral]. rewrite!Arithmetic.add_succ,Arithmetic.add_zero.
   intro E. do 2 apply(Model.succ_injective M)in E. exact(Model.zero_ne_succ M(succM M q)(eq_sym E)).
Qed.
Theorem projection_representative_fixes_child_relative M f child relative k r b c n d e l:
 source_bounded M f k ->source_quantifier_matrix M(code_numeral M 1)f child ->
 source_set_relativization M(code_numeral M 3)child relative ->
 renaming_lift M r r(code_numeral M 1)(zeroM M)b c n ->renaming_lift M b c n(zeroM M)d e l ->
 numerical_renaming M relative d e l(zeroM M)relative.
Proof.
 intros BF HC HR H1 H2.
 destruct(source_set_relativization_renaming_exists M child(code_numeral M 3)(code_numeral M 3)d e l(zeroM M)child relative
  (projection_representative_two_fixed M r b c n d e l(code_numeral M 3)H1 H2(source_fixed_numeral_neq M 3 2 ltac:(discriminate)))
  (projection_representative_fixes_child_matrix M f child k r b c n d e l BF HC H1 H2)HR)as(other&HO&HM).
 rewrite(source_set_relativization_functional M child(code_numeral M 3)other relative HO HR)in HM. exact HM.
Qed.
Print Assumptions projection_representative_fixes_environment.
Print Assumptions projection_representative_fixes_child_matrix.
Print Assumptions projection_representative_fixes_child_relative.
