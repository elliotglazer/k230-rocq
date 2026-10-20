(** Identity-parameter witness extraction, including the literal common-level
    membership block produced by the cofinal theorem. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions NumericalProofs SetFormulaCodes SourceBounded
 NumericalEnvironments NumericalSubstitutionMaps NumericalSubstitution NumericalSourceFull NumericalContexts
 SourceSubstitutionIdentity SourceBallSMembershipBlock SourceMembershipBlocks SourceMembershipBlockProofs
 SourceHierarchySyntax SourcePieceClosure SourceEwMonotone SourcePieceWitnessParameters.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
Theorem source_full_pc_initial_parameter_witness M domain level count phi d X pc Y lev ew gb gc gn:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
 source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_bounded M phi(succM M count) ->
 source_pc_instance M domain level count phi d X pc ->source_LL_instance M d Y lev ->source_ew_at M domain phi Y ew ->
 source_full_prv M gb gc gn pc ->source_full_prv M gb gc gn lev ->
 (forall i member,coding_lt M i count ->sf_relation M SFMember i X member ->source_full_prv M gb gc gn member) ->
 source_full_prv M gb gc gn ew.
Proof.
 intros HD HL HLg HB HPC HLev HEw PP PL PM.
 destruct(balls_offset_assignment_total M(zeroM M)count)as(pb&pc0&HOffset).
 destruct(substitution_lift_total M pb pc0 count(zeroM M))as(ub&uc&un&HU).
 assert(HId:numerical_substitution M phi ub uc un(code_numeral M 1)phi).
 { apply(numerical_substitution_identity_on_bound M phi ub uc un(code_numeral M 1)(succM M count)HB).
   intros i HI.
   destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)as[E|[j E]];subst i.
   - exact(proj2(substitution_lift_head M _ _ _ _ _ _ _ _ HU)eq_refl).
   - apply(proj2(substitution_lift_tail M _ _ _ _ _ _ _ _ _ HU)).
     assert(HJ:coding_lt M j count)by(exact(proj1(coding_lt_succ_cancel M j count)HI)).
     apply(proj2(substitution_lookup_inside M pb pc0 count(zeroM M)j j HJ)).
     apply(proj2(HOffset j j HJ)). symmetry. apply coding_add_zero_r. }
 apply(source_full_pc_parameter_witness M domain level count phi d X pc pb pc0 ub uc un phi Y lev ew
  gb gc gn(succM M count)HD HL HLg HB HB HPC HU HId);try assumption.
 intros i value member HI HE HMember. pose proof(proj1(HOffset i value HI)HE)as E.
 rewrite coding_add_zero_r in E. subst value. exact(PM i member HI HMember).
Qed.
Theorem source_full_pc_membership_block_witness M domain level count phi d X pc Y lev ew block gb gc gn k:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
 source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_bounded M phi(succM M count) ->
 source_pc_instance M domain level count phi d X pc ->source_LL_instance M d Y lev ->source_ew_at M domain phi Y ew ->
 source_membership_block M(zeroM M)X count block ->context_bounded M gb gc gn k ->coding_lt M X k ->
 (forall i,coding_lt M i count ->coding_lt M i k) ->
 source_full_prv M gb gc gn pc ->source_full_prv M gb gc gn lev ->source_full_prv M gb gc gn block ->
 source_full_prv M gb gc gn ew.
Proof.
 intros HD HL HLg HB HPC HLev HEw HBlock HC HX HNames PP PL PB.
 apply(source_full_pc_initial_parameter_witness M domain level count phi d X pc Y lev ew gb gc gn
  HD HL HLg HB HPC HLev HEw PP PL).
 intros i member HI HM.
 apply(source_full_membership_block_project M(zeroM M)X count block gb gc gn k i member);
 try assumption.
 - intros j HJ. rewrite coding_add_zero_r. exact(HNames j HJ).
 - now rewrite coding_add_zero_r.
Qed.
Print Assumptions source_full_pc_initial_parameter_witness.
Print Assumptions source_full_pc_membership_block_witness.
