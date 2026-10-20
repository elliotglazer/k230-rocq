(** Checked insertion of the new head assignment above the fixed
    A/S/C frame. The original EnvF source code remains arbitrary. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceNumeralLift
 SourceSubstitutionIdentity SourceFiniteCutoffShift SourceCutoffShiftCommutation SourceEnvFScopedHole SourceEnvInClosureRoleMaps
 SourceRenamingIdentity SourceRenamingDiamond SourceShiftSpecialization NumericalRenamingMaps NumericalRenaming
 NumericalSubstitutionMaps NumericalSubstitution RenamingSubstitution SourceMembershipBlocks SourceMembershipBlockProofs.
From Stdlib Require Import Lia.
From FOL.Tennenbaum Require Peano.
Unset Implicit Arguments.
Lemma eic_parameter_tail_value M padding i:
 addM M(succM M i)(code_numeral M padding)=source_succ_iter M(S padding)i.
Proof.
 induction padding as[|padding IH].
 - cbn[source_succ_iter code_numeral]. apply coding_add_zero_r.
 - change(addM M(succM M i)(succM M(code_numeral M padding))=succM M(source_succ_iter M(S padding)i)).
   rewrite Arithmetic.add_comm,Arithmetic.add_succ,Arithmetic.add_comm,IH. reflexivity.
Qed.
Theorem source_low_parameter_shift_boundary_insert M padding f lower result k:
 source_bounded M f k->source_low_parameter_shift M padding f lower->
 source_cutoff_shift M(S padding)lower result->source_low_parameter_shift M(S padding)f result.
Proof.
 intros BF HL(b&c&n&HM&HS).
 pose proof(source_cutoff_shift_map_renaming M(S padding)lower result b c n HM HS)as HT.
 assert(HId:numerical_renaming M f(zeroM M)(zeroM M)(zeroM M)(zeroM M)f).
 { apply(numerical_renaming_identity_on_bound M f _ _ _ _ k BF). intros i _. apply source_empty_renaming_lookup. }
 apply(numerical_source_renaming_diamond M f k
  (zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M padding)
  (zeroM M)(zeroM M)(zeroM M)(zeroM M)
  b c n(code_numeral M 1)
  (zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M(S padding))lower f result BF HL HId HT).
 intros i j l m HI HJ HM' HI0.
 rewrite(renaming_lookup_functional M _ _ _ _ i l i HI0(source_empty_renaming_lookup M i)).
 apply(proj1(source_cutoff_shift_map_renaming_lookup M(S padding)b c n j m HM))in HM'.
 destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)as[->|[q ->]].
 - rewrite(renaming_lookup_functional M _ _ _ _ _ j _ HJ(low_parameter_lookup_zero M padding))in HM'.
   pose proof(source_cutoff_shift_map_fixed_lookup M(S padding)b c n HM 0)as HFix.
   change(substitution_lookup M b c n(code_numeral M(S(S padding)))(zeroM M)(zeroM M))in HFix.
   rewrite(substitution_lookup_functional M _ _ _ _ _ m _ HM' HFix). apply low_parameter_lookup_zero.
 - rewrite(renaming_lookup_functional M _ _ _ _ _ j _ HJ(low_parameter_lookup_nonzero M padding(succM M q)(env_role_nonzero M q)))in HM'.
   rewrite eic_parameter_tail_value in HM'.
   pose proof(source_cutoff_shift_map_tail_lookup M(S padding)b c n q HM)as HFix.
   rewrite(substitution_lookup_functional M _ _ _ _ _ m _ HM' HFix).
   pose proof(low_parameter_lookup_nonzero M(S padding)(succM M q)(env_role_nonzero M q))as HO.
   now rewrite eic_parameter_tail_value in HO.
Qed.
Lemma eic_shift_index_below depth i:(i<depth)%nat->sf_index(source_shift_sigma depth i)=i.
Proof.
 revert i. induction depth as[|depth IH];intros[|i]HI;try lia;[reflexivity|].
 specialize(IH i ltac:(lia)).
 destruct(source_shift_sigma depth i)as[j|[]]eqn:E.
 change(j=i)in IH. subst j.
 change(sf_index(Core.subst_term(fun j=>Core.var(S j))(source_shift_sigma depth i))=S i).
 rewrite E. reflexivity.
Qed.
Theorem source_cutoff_shift_fixes_bounded M depth f:
 source_bounded M f(code_numeral M depth)->source_cutoff_shift M depth f f.
Proof.
 intro BF. destruct(source_cutoff_shift_map_total M depth)as(b&c&n&HM). exists b,c,n. split;[exact HM|].
 apply(numerical_substitution_identity_on_bound M f b c n(code_numeral M(S depth))(code_numeral M depth)BF).
 intros i HI. destruct(source_numeral_initial_segment M depth i HI)as(v&HV&->).
 pose proof(source_cutoff_shift_map_fixed_lookup M depth b c n HM v)as H.
 now rewrite(eic_shift_index_below depth v HV)in H.
Qed.
Theorem source_membership_block_tail_cutoff M count block tail:
 source_membership_block M(code_numeral M 3)(zeroM M)count block->
 source_membership_block M(code_numeral M 4)(zeroM M)count tail->source_cutoff_shift M 3 block tail.
Proof.
 intros HB HT. destruct(source_cutoff_shift_map_total M 3)as(b&c&n&HM).
 assert(HRen:numerical_renaming M block b c n(code_numeral M 1)tail).
 { apply(source_membership_block_renaming M(code_numeral M 3)(zeroM M)count block(code_numeral M 4)(zeroM M)tail b c n(code_numeral M 1)HB HT).
   - apply(proj2(source_cutoff_shift_map_renaming_lookup M 3 b c n _ _ HM)).
     exact(source_cutoff_shift_map_fixed_lookup M 3 b c n HM 0).
   - intros i HI. apply(proj2(source_cutoff_shift_map_renaming_lookup M 3 b c n _ _ HM)).
     replace(addM M i(code_numeral M 3))with(source_succ_iter M 3 i).
     2:{ rewrite Arithmetic.add_comm. cbn[source_succ_iter code_numeral]. now rewrite!Arithmetic.add_succ,Arithmetic.add_zero. }
     replace(addM M i(code_numeral M 4))with(source_succ_iter M 4 i).
     2:{ rewrite Arithmetic.add_comm. cbn[source_succ_iter code_numeral]. now rewrite!Arithmetic.add_succ,Arithmetic.add_zero. }
     exact(source_cutoff_shift_map_tail_lookup M 3 b c n i HM). }
 exists b,c,n. split;[exact HM|].
 pose proof(proj1(numerical_renaming_substitution M block b c n(code_numeral M 1)tail)HRen)as HS.
 rewrite(source_cutoff_shift_map_length M 3 b c n HM)in HS|-*.
 change(numerical_substitution M block b c(code_numeral M 3)(code_numeral M 4)tail).
 change(numerical_substitution M block b c(code_numeral M 3)(addM M(code_numeral M 3)(code_numeral M 1))tail)in HS.
 cbn[code_numeral]in HS. now rewrite!Arithmetic.add_succ,Arithmetic.add_zero in HS.
Qed.
Print Assumptions source_low_parameter_shift_boundary_insert.
Print Assumptions source_cutoff_shift_fixes_bounded.
Print Assumptions source_membership_block_tail_cutoff.
