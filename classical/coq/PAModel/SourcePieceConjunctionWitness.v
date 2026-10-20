(** Real PCf table projection followed by all parameter/level eliminations. *)
From PAModel Require Import Model FiniteCoding CodeExpressions Pairing SetFormulaCodes SourceBounded NumericalContexts NumericalSourceFull
 SourceHierarchySyntax SourcePieceClosure SourcePieceConjunction SourcePieceConjunctionBounds SourcePieceConjunctionProofs
 SourceMembershipBlocks SourceEwMonotone SourcePieceWitnessIdentity.
Unset Implicit Arguments.
Theorem source_full_pcf_initial_parameter_witness M domain level sb sc count d X all entry params phi Y lev ew gb gc gn k:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
 source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_piece_table_valid M sb sc count ->
 coding_lt M d k ->coding_lt M X k ->context_bounded M gb gc gn k ->
 context_member M sb sc count entry ->pair_graph M params phi entry ->
 source_piece_conjunction M domain level sb sc count d X all ->source_LL_instance M d Y lev ->source_ew_at M domain phi Y ew ->
 source_full_prv M gb gc gn all ->source_full_prv M gb gc gn lev ->
 (forall i member,coding_lt M i params ->sf_relation M SFMember i X member ->source_full_prv M gb gc gn member) ->
 source_full_prv M gb gc gn ew.
Proof.
 intros HD HL HLg HV BD BX HC HMember HPair HAll HLev HEw PP PL PM.
 pose proof(HV entry params phi HMember HPair)as HB.
 destruct(source_pc_instance_total M domain level params phi d X)as(pc&HPC).
 pose proof(source_piece_conjunction_project M count domain level sb sc d X all gb gc gn k
  HD HL HV BD BX HC HAll PP entry params phi pc HMember HPair HPC)as PPC.
 exact(source_full_pc_initial_parameter_witness M domain level params phi d X pc Y lev ew gb gc gn
  HD HL HLg HB HPC HLev HEw PPC PL PM).
Qed.
Print Assumptions source_full_pcf_initial_parameter_witness.
