(** Actual Refl specializes to the exact noncontiguous L Separation
    matrix: output name0 and parameter names4,5,...; carrier name2. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 NumericalContexts NumericalSourceFull NumericalSubstitutionMaps SourceSubstitutionBounds SourceMembershipBlocks SourceMembershipBlockProofs
 SourceLFixed SourceD0Recipe SourceRelativization SourceSetRelativization SourceIffGraphs SourceHierarchySyntax SourceOrdinaryReflectionSyntax
 SourceOrdinaryReflectionSubstitution SourceLSeparationReflectionMap.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
Local Opaque source_L_domain_code.
Theorem source_full_L_separation_reflection_point M phi matrix params d refl level block lp sp equiv member gb gc gn width:
 source_bounded M phi(succM M params) ->context_bounded M gb gc gn width ->coding_lt M d width ->
 coding_lt M(code_numeral M 2)width ->
 (forall i,coding_lt M i params ->coding_lt M(succM M(succM M(succM M(succM M i))))width) ->
 source_cutoff_shift_thrice M phi matrix ->source_ordinary_reflection M(source_L_domain_code M)(succM M params)phi d refl ->
 source_LL_instance M d(code_numeral M 2)level ->source_membership_block M(code_numeral M 4)(code_numeral M 2)params block ->
 source_relativization M(source_L_domain_code M)matrix lp ->source_set_relativization M(code_numeral M 2)matrix sp ->
 source_iff_graph M lp sp equiv ->sf_relation M SFMember(zeroM M)(code_numeral M 2)member ->
 source_full_prv M gb gc gn refl ->source_full_prv M gb gc gn level ->source_full_prv M gb gc gn block ->
 source_full_prv M gb gc gn member ->source_full_prv M gb gc gn equiv.
Proof.
 intros HP HC BD B2 HNames HMatrix HRefl HL HB HLP HSP HE HM PR PL PB PM.
 pose proof(source_lsep_matrix_substitution M phi matrix(succM M params)HP HMatrix)as HS.
 assert(B0:coding_lt M(zeroM M)width).
 { exact(coding_lt_trans M(zeroM M)(code_numeral M 2)width(coding_zero_lt_succ M(code_numeral M 1))B2). }
 assert(HMap:substitution_maps_bound M(zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M 4)(succM M params)width).
 { intros i v HI HV.
   destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)as[E|[idx E]];subst i.
   - assert(E:v=zeroM M)by(exact(substitution_lookup_functional M(zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M 4)
      (zeroM M)v(zeroM M)HV(source_lsep_matrix_lookup_zero M))). now subst v.
   - assert(E:v=succM M(succM M(succM M(succM M idx))))by(exact(substitution_lookup_functional M(zeroM M)(zeroM M)
      (code_numeral M 1)(code_numeral M 4)(succM M idx)v _ HV(source_lsep_matrix_lookup_succ M idx))). subst v.
     exact(HNames idx(proj1(coding_lt_succ_cancel M idx params)HI)). }
 apply(source_full_ordinary_reflection_substitution M(source_L_domain_code M)(succM M params)phi d refl(code_numeral M 2)level
   (zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M 4)matrix lp sp equiv gb gc gn width
   (numerical_L_domain_bounded M)HP HC BD B2 HMap HRefl HL HS HLP HSP HE PR PL).
 intros i v member' HI HV HM'.
 destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)as[E|[idx E]];subst i.
 - assert(E:v=zeroM M)by(exact(substitution_lookup_functional M(zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M 4)
    (zeroM M)v(zeroM M)HV(source_lsep_matrix_lookup_zero M))). subst v.
   assert(E:member'=member)by(eapply sf_relation_functional;eassumption). now subst member'.
 - assert(E:v=succM M(succM M(succM M(succM M idx))))by(exact(substitution_lookup_functional M(zeroM M)(zeroM M)
    (code_numeral M 1)(code_numeral M 4)(succM M idx)v _ HV(source_lsep_matrix_lookup_succ M idx))). subst v.
   assert(HOffset:forall j,addM M j(code_numeral M 4)=succM M(succM M(succM M(succM M j)))).
   { intro j. rewrite Arithmetic.add_comm. change(addM M(succM M(succM M(succM M(succM M(zeroM M)))))j=succM M(succM M(succM M(succM M j)))).
     rewrite !Arithmetic.add_succ,Arithmetic.add_zero. reflexivity. }
   apply(source_full_membership_block_project M(code_numeral M 4)(code_numeral M 2)params block gb gc gn width idx member').
   + intros j HJ. rewrite HOffset. exact(HNames j HJ).
   + exact B2.
   + exact HB.
   + exact HC.
   + exact PB.
   + exact(proj1(coding_lt_succ_cancel M idx params)HI).
   + rewrite HOffset. exact HM'.
Qed.
Print Assumptions source_full_L_separation_reflection_point.
