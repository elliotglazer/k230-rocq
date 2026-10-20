(** Actual arbitrary-code role maps for the EnvF-in-C successor.
    Padding inserts unused parameter slots; the environment witness0
    is treated separately from its internally many assignment values. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SourceBounded
 NumericalRenamingMaps NumericalRenaming SourceRenamingIdentity SourceRenamingDiamond SourceShiftSpecialization
 SourceFiniteCutoffShift SourceCutoffShiftCommutation SourceEnvFScopedHole RawBinderRenaming SourceNamedQuantifierRules.
From FOL.Tennenbaum Require Peano.
Unset Implicit Arguments.
Definition source_env_witness_renaming M name padding f named:=
 numerical_renaming M f name name(code_numeral M 1)(code_numeral M padding)named.
Lemma env_role_nonzero M i:succM M i<>zeroM M.
Proof. intro E. exact(Model.zero_ne_succ M i(eq_sym E)). Qed.
Theorem source_env_witness_low_composition M padding f lower named name k:
 source_bounded M f k->source_low_parameter_shift M padding f lower->
 numerical_renaming M lower name name(code_numeral M 1)(zeroM M)named->
 source_env_witness_renaming M name padding f named.
Proof.
 intros BF HL HN. assert(HId:numerical_renaming M f(zeroM M)(zeroM M)(zeroM M)(zeroM M)f).
 { apply(numerical_renaming_identity_on_bound M f _ _ _ _ k BF). intros i _. apply source_empty_renaming_lookup. }
 apply(numerical_source_renaming_diamond M f k
  (zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M padding)
  (zeroM M)(zeroM M)(zeroM M)(zeroM M)
  name name(code_numeral M 1)(zeroM M)
  name name(code_numeral M 1)(code_numeral M padding)lower f named BF HL HId HN).
 intros i j l m HI HJ HM HI0.
 rewrite(renaming_lookup_functional M _ _ _ _ i l i HI0(source_empty_renaming_lookup M i)).
 destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)as[->|[q ->]].
 - rewrite(renaming_lookup_functional M _ _ _ _ _ j _ HJ(low_parameter_lookup_zero M padding))in HM.
   rewrite(renaming_lookup_functional M _ _ _ _ _ m name HM ltac:(left;split;[apply coding_zero_lt_succ|apply beta_singleton])).
   left. split;[apply coding_zero_lt_succ|apply beta_singleton].
 - pose proof(low_parameter_lookup_nonzero M padding(succM M q)(env_role_nonzero M q))as HJ'.
   rewrite(renaming_lookup_functional M _ _ _ _ _ j _ HJ HJ')in HM.
   assert(HP:addM M(succM M q)(code_numeral M padding)<>zeroM M).
   { rewrite Arithmetic.add_succ. apply env_role_nonzero. }
   assert(HM':renaming_lookup M name name(code_numeral M 1)(zeroM M)
    (addM M(succM M q)(code_numeral M padding))(addM M(succM M q)(code_numeral M padding))).
   { right. split;[|symmetry;apply coding_add_zero_r]. intro H. apply coding_lt_succ_cases in H.
     destruct H as[H|H];[exact(coding_not_lt_zero M _ H)|contradiction]. }
   rewrite(renaming_lookup_functional M _ _ _ _ _ m _ HM HM').
   right. split;[|reflexivity]. intro H. apply coding_lt_succ_cases in H.
   destruct H as[H|H];[exact(coding_not_lt_zero M _ H)|exact(env_role_nonzero M q H)].
Qed.
Theorem source_env_witness_closing M padding f named closed name k rb rc:
 source_bounded M f k->source_env_witness_renaming M name padding f named->
 source_low_parameter_shift M(S padding)f closed->raw_binder_renaming M name rb rc->
 (forall i,coding_lt M i k->i<>zeroM M->addM M i(code_numeral M padding)<>name)->
 numerical_renaming M named rb rc(succM M name)(code_numeral M 1)closed.
Proof.
 intros BF HN HC HRaw HFresh.
 assert(HId:numerical_renaming M f(zeroM M)(zeroM M)(zeroM M)(zeroM M)f).
 { apply(numerical_renaming_identity_on_bound M f _ _ _ _ k BF). intros i _. apply source_empty_renaming_lookup. }
 apply(numerical_source_renaming_diamond M f k
  (zeroM M)(zeroM M)(zeroM M)(zeroM M)
  name name(code_numeral M 1)(code_numeral M padding)
  (zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M(S padding))
  rb rc(succM M name)(code_numeral M 1)f named closed BF HId HN HC).
 intros i j l m HI HJ HM HL.
 rewrite(renaming_lookup_functional M _ _ _ _ i j i HJ(source_empty_renaming_lookup M i))in HM.
 apply(proj2(HRaw l m)).
 destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)as[->|[q ->]].
 - rewrite(renaming_lookup_functional M _ _ _ _ _ l name HL ltac:(left;split;[apply coding_zero_lt_succ|apply beta_singleton])).
   rewrite(renaming_lookup_functional M _ _ _ _ _ m _ HM(low_parameter_lookup_zero M(S padding))). left;auto.
 - assert(HN0:succM M q<>zeroM M)by(apply env_role_nonzero).
   assert(HL':renaming_lookup M name name(code_numeral M 1)(code_numeral M padding)
    (succM M q)(addM M(succM M q)(code_numeral M padding))).
   { right. split;[|reflexivity]. intro H. apply coding_lt_succ_cases in H.
     destruct H as[H|H];[exact(coding_not_lt_zero M _ H)|contradiction]. }
   rewrite(renaming_lookup_functional M _ _ _ _ _ l _ HL HL').
   rewrite(renaming_lookup_functional M _ _ _ _ _ m _ HM(low_parameter_lookup_nonzero M(S padding)(succM M q)HN0)).
   right. split;[exact(HFresh _ HI HN0)|].
   change(addM M(succM M q)(succM M(code_numeral M padding))=succM M(addM M(succM M q)(code_numeral M padding))).
   rewrite Arithmetic.add_comm,Arithmetic.add_succ,Arithmetic.add_comm. reflexivity.
Qed.
Print Assumptions source_env_witness_low_composition.
Print Assumptions source_env_witness_closing.
