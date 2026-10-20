(** The literal RR relation used by the genuine recursion Replacement instance. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 NumericalSubstitutionMaps NumericalSubstitution NumericalRenaming RenamingSubstitution SourceQuantifierRules
 SourceRecursionAttemptApp SourceRecursionShiftGraphs SourceRecursionAtomicShift.
Unset Implicit Arguments.
Definition source_rec_rr M phi z v o a N out:=exists member witness,
 sf_relation M SFMember z N member /\source_rec_attempt_app M phi z v o a N witness /\sf_relation M SFAnd member witness out.
Theorem source_rec_rr_total M phi z v o a N:exists out,source_rec_rr M phi z v o a N out.
Proof.
 destruct(sf_relation_total M SFMember z N)as(member&HM).
 destruct(source_rec_attempt_app_total M phi z v o a N)as(witness&HW).
 destruct(sf_relation_total M SFAnd member witness)as(out&HO). exists out,member,witness. auto.
Qed.
Theorem source_rec_rr_functional M phi z v o a N x y:
 source_rec_rr M phi z v o a N x ->source_rec_rr M phi z v o a N y ->x=y.
Proof.
 intros(member&witness&HM&HW&HX)(member'&witness'&HM'&HW'&HY).
 pose proof(sf_relation_functional M SFMember z N member' member HM' HM)as E. subst member'.
 pose proof(source_rec_attempt_app_functional M phi z v o a N witness' witness HW' HW)as E. subst witness'.
 exact(sf_relation_functional M SFAnd member witness x y HX HY).
Qed.
Theorem source_rec_rr_bounded M phi z v o a N out k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M z k ->coding_lt M v k ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->
 source_rec_rr M phi z v o a N out ->source_bounded M out k.
Proof.
 intros BP BZ BV BO BA BN(member&witness&HM&HW&HO).
 exact(proj2(source_bounded_accept_binary M SFAnd member witness out k(or_introl eq_refl)HO)
  (conj(proj2(source_bounded_accept_atom M SFMember z N member k(or_introl eq_refl)HM)(conj BZ BN))
  (source_rec_attempt_app_bounded M phi z v o a N witness k BP BZ BV BO BA BN HW))).
Qed.
Theorem source_rec_rr_substitution M phi z v o a N old z' v' o' a' N' new rb rc rn base:
 source_bounded M phi(code_numeral M 2) ->source_rec_rr M phi z v o a N old ->source_rec_rr M phi z' v' o' a' N' new ->
 substitution_lookup M rb rc rn base z z' ->substitution_lookup M rb rc rn base v v' ->substitution_lookup M rb rc rn base o o' ->
 substitution_lookup M rb rc rn base a a' ->substitution_lookup M rb rc rn base N N' ->numerical_substitution M old rb rc rn base new.
Proof.
 intros BP(member&witness&HM&HW&HO)(member'&witness'&HM'&HW'&HO')HZ HV HOO HAA HNN.
 apply(proj2(numerical_substitution_binary M SFAnd member witness old rb rc rn base new(or_introl eq_refl)HO)).
 exists member',witness'. split;[|split;[|exact HO']].
 - apply(proj2(numerical_substitution_member M z N member rb rc rn base member' HM)). exists z',N'. auto.
 - exact(source_rec_attempt_app_substitution M phi z v o a N witness z' v' o' a' N' witness' rb rc rn base BP HW HW' HZ HV HOO HAA HNN).
Qed.
Theorem source_rec_rr_shift M phi z v o a N old new:
 source_bounded M phi(code_numeral M 2) ->source_rec_rr M phi z v o a N old ->
 source_rec_rr M phi(succM M z)(succM M v)(succM M o)(succM M a)(succM M N)new ->source_formula_shift M old new.
Proof.
 intros BP HO HN. apply(proj2(numerical_renaming_substitution M old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new)). rewrite Arithmetic.add_zero.
 exact(source_rec_rr_substitution M phi z v o a N old(succM M z)(succM M v)(succM M o)(succM M a)(succM M N)new
  (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)BP HO HN(source_rec_shift_lookup M z)(source_rec_shift_lookup M v)(source_rec_shift_lookup M o)(source_rec_shift_lookup M a)(source_rec_shift_lookup M N)).
Qed.
Print Assumptions source_rec_rr_total.
Print Assumptions source_rec_rr_functional.
Print Assumptions source_rec_rr_bounded.
Print Assumptions source_rec_rr_substitution.
Print Assumptions source_rec_rr_shift.
