(** Uniform Leibniz transport in the output coordinate of an internal binary matrix. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceNumeralLift
 NumericalSubstitutionMaps NumericalSubstitution SourceRoleReopening SourcePieceClosure SourcePieceClosureFacts
 SourceRecursionBinaryInstance SourceConditionalProofs SourceEqualityCongruence SourceEqualitySupport SourceEqualityAtomFacts
 SourceBinaryEqualityTransport SourceZFRProvability.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_binary_output_equality M phi u v v' before after condition q:
 source_bounded M phi(code_numeral M 2) ->coding_lt M u q ->coding_lt M v q ->coding_lt M v' q ->
 source_rec_binary M phi u v before ->source_rec_binary M phi u v' after ->sf_relation M SFEqual v v' condition ->
 source_conditional_equivalent M condition before after.
Proof.
 intros BP BU BV BV' HA HB HC.
 pose proof(source_rec_binary_bounded M phi u v before q BP BU BV HA)as BA.
 pose proof(source_rec_binary_bounded M phi u v' after q BP BU BV' HB)as BB.
 pose proof(proj2(source_bounded_accept_atom M SFEqual v v' condition q(or_intror eq_refl)HC)(conj BV BV'))as BC.
 destruct HA as(ab&ac&HRoleA&HSubA). destruct HB as(bb&bc&HRoleB&HSubB).
 apply(source_equality_congruence_internal M phi condition(code_numeral M 2)
  ab ac(code_numeral M 2)(code_numeral M 2)bb bc(code_numeral M 2)(code_numeral M 2)before after q BP BC BA BB HSubA HSubB).
 intros i x y equal HI HX HY HE.
 destruct(source_numeral_initial_segment M 2 i HI)as(n&HN&->).
 pose proof(substitution_lookup_functional M _ _ _ _ _ x(if Nat.eqb n 0 then u else v)
  HX(source_pc_reopening_lookup M v u ab ac(code_numeral M 2)n HRoleA HN))as EX.
 pose proof(substitution_lookup_functional M _ _ _ _ _ y(if Nat.eqb n 0 then u else v')
  HY(source_pc_reopening_lookup M v' u bb bc(code_numeral M 2)n HRoleB HN))as EY.
 subst x y. destruct n as[|[|n]];try lia.
 - apply(source_conditional_fact_of_proof M condition equal q BC).
   + exact(proj2(source_bounded_accept_atom M SFEqual u u equal q(or_intror eq_refl)HE)(conj BU BU)).
   + exact(source_zfr_equal_reflexive M u equal HE).
 - pose proof(sf_relation_functional M SFEqual v v' equal condition HE HC)as E. subst equal.
   exact(source_conditional_fact_self M condition q BC).
Qed.
Theorem source_zfr_binary_output_equality M phi u v v' before after condition point law q:
 source_bounded M phi(code_numeral M 2) ->coding_lt M u q ->coding_lt M v q ->coding_lt M v' q ->
 source_rec_binary M phi u v before ->source_rec_binary M phi u v' after ->sf_relation M SFEqual v v' condition ->
 sf_relation M SFImpl before after point ->sf_relation M SFImpl condition point law ->source_zfr_provable M law.
Proof.
 intros BP BU BV BV' HA HB HC HP HL.
 exact(proj1(source_binary_output_equality M phi u v v' before after condition q BP BU BV BV' HA HB HC)point HP law HL).
Qed.
Print Assumptions source_binary_output_equality.
Print Assumptions source_zfr_binary_output_equality.
