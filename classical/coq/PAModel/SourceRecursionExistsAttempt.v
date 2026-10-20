(** Literal ExA for arbitrary internal binary matrices. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded NumericalSubstitutionMaps NumericalSubstitution
 NumericalRenaming RenamingSubstitution SourceQuantifierRules SourceRecursionPrimitiveRelations SourceRecursionAttempt SourceRecursionAttemptBounds
 SourceRecursionAttemptTransport SourceRecursionAppExists SourceRecursionShiftGraphs.
Unset Implicit Arguments.
Definition source_rec_exa M phi z o a N out:=exists att some body,
 source_rec_attempt M phi(succM M o)(succM M a)(succM M N)(zeroM M)att /\source_rec_app_exists M(zeroM M)(succM M z)some /\
 sf_relation M SFAnd att some body /\sf_relation M SFEx body(zeroM M)out.
Theorem source_rec_exa_total M phi z o a N:exists out,source_rec_exa M phi z o a N out.
Proof.
 destruct(source_rec_attempt_total M phi(succM M o)(succM M a)(succM M N)(zeroM M))as(att&HT).
 destruct(source_rec_app_exists_total M(zeroM M)(succM M z))as(some&HS).
 destruct(sf_relation_total M SFAnd att some)as(body&HB).
 destruct(sf_relation_total M SFEx body(zeroM M))as(out&HO). exists out,att,some,body. auto.
Qed.
Theorem source_rec_exa_bounded M phi z o a N out k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M z k ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->source_rec_exa M phi z o a N out ->source_bounded M out k.
Proof.
 intros BP BZ BO BA BN(att&some&body&HT&HS&HB&HO).
 pose proof(source_rec_attempt_bounded M phi(succM M o)(succM M a)(succM M N)(zeroM M)att(succM M k)BP
  (proj2(coding_lt_succ_cancel M o k)BO)(proj2(coding_lt_succ_cancel M a k)BA)(proj2(coding_lt_succ_cancel M N k)BN)(coding_zero_lt_succ M k)HT)as BT.
 pose proof(source_rec_app_exists_bounded M(zeroM M)(succM M z)some(succM M k)(coding_zero_lt_succ M k)(proj2(coding_lt_succ_cancel M z k)BZ)HS)as BS.
 exact(proj2(source_bounded_accept_unary M SFEx body out k(or_intror eq_refl)HO)(proj2(source_bounded_accept_binary M SFAnd att some body(succM M k)(or_introl eq_refl)HB)(conj BT BS))).
Qed.
Theorem source_rec_exa_substitution M phi z o a N old z' o' a' N' new rb rc rn base:
 source_bounded M phi(code_numeral M 2) ->source_rec_exa M phi z o a N old ->source_rec_exa M phi z' o' a' N' new ->
 substitution_lookup M rb rc rn base z z' ->substitution_lookup M rb rc rn base o o' ->substitution_lookup M rb rc rn base a a' ->substitution_lookup M rb rc rn base N N' ->
 numerical_substitution M old rb rc rn base new.
Proof.
 intros BP(att&some&body&HT&HS&HB&HO)(att'&some'&body'&HT'&HS'&HB'&HO')HZ HOO HA HN.
 destruct(substitution_lift_total M rb rc rn base)as(lb&lc&ln&HL).
 apply(proj2(numerical_substitution_quantifier M false body old rb rc rn base new HO)). exists lb,lc,ln,body'. split;[exact HL|]. split;[|exact HO'].
 apply(proj2(numerical_substitution_binary M SFAnd att some body lb lc ln(succM M base)body'(or_introl eq_refl)HB)). exists att',some'.
 split;[|split;[|exact HB']].
 - exact(source_rec_attempt_substitution M phi(succM M o)(succM M a)(succM M N)(zeroM M)att(succM M o')(succM M a')(succM M N')(zeroM M)att'
    lb lc ln(succM M base)BP HT HT'(proj2(proj2 HL)o o' HOO)(proj2(proj2 HL)a a' HA)(proj2(proj2 HL)N N' HN)(proj1(proj2 HL))).
 - exact(source_rec_app_exists_substitution M(zeroM M)(succM M z)some(zeroM M)(succM M z')some' lb lc ln(succM M base)HS HS'(proj1(proj2 HL))(proj2(proj2 HL)z z' HZ)).
Qed.
Theorem source_rec_exa_shift M phi z o a N old new:
 source_bounded M phi(code_numeral M 2) ->source_rec_exa M phi z o a N old ->source_rec_exa M phi(succM M z)(succM M o)(succM M a)(succM M N)new ->source_formula_shift M old new.
Proof.
 intros BP HO HN. apply(proj2(numerical_renaming_substitution M old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new)). rewrite Arithmetic.add_zero.
 exact(source_rec_exa_substitution M phi z o a N old(succM M z)(succM M o)(succM M a)(succM M N)new(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)
 BP HO HN(source_rec_shift_lookup M z)(source_rec_shift_lookup M o)(source_rec_shift_lookup M a)(source_rec_shift_lookup M N)).
Qed.
Print Assumptions source_rec_exa_total.
Print Assumptions source_rec_exa_bounded.
Print Assumptions source_rec_exa_substitution.
Print Assumptions source_rec_exa_shift.
