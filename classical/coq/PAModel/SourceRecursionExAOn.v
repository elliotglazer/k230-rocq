(** Attempt existence at every index of a named recursion domain. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 NumericalSubstitutionMaps NumericalSubstitution NumericalRenaming RenamingSubstitution SourceQuantifierRules
 SourceRecursionPrimitiveRelations SourceRecursionExistsAttempt SourceRecursionShiftGraphs.
Unset Implicit Arguments.
Definition source_rec_exa_on M phi o a N out:=exists member agr point,
 sf_relation M SFMember(zeroM M)(succM M N)member /\source_rec_exa M phi(zeroM M)(succM M o)(succM M a)(succM M N)agr /\
 sf_relation M SFImpl member agr point /\sf_relation M SFAll point(zeroM M)out.
Theorem source_rec_exa_on_total M phi o a N:exists out,source_rec_exa_on M phi o a N out.
Proof.
 destruct(sf_relation_total M SFMember(zeroM M)(succM M N))as(member&HM).
 destruct(source_rec_exa_total M phi(zeroM M)(succM M o)(succM M a)(succM M N))as(agr&HA).
 destruct(sf_relation_total M SFImpl member agr)as(point&HP).
 destruct(sf_relation_total M SFAll point(zeroM M))as(out&HO). exists out,member,agr,point. auto.
Qed.
Theorem source_rec_exa_on_bounded M phi o a N out k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->source_rec_exa_on M phi o a N out ->source_bounded M out k.
Proof.
 intros BP BO BA BN(member&agr&point&HM&HA&HP&HO).
 assert(BM:source_bounded M member(succM M k))by exact(proj2(source_bounded_accept_atom M SFMember _ _ member(succM M k)(or_introl eq_refl)HM)
  (conj(coding_zero_lt_succ M k)(proj2(coding_lt_succ_cancel M N k)BN))).
 pose proof(source_rec_exa_bounded M phi(zeroM M)(succM M o)(succM M a)(succM M N)agr(succM M k)BP(coding_zero_lt_succ M k)
  (proj2(coding_lt_succ_cancel M o k)BO)(proj2(coding_lt_succ_cancel M a k)BA)(proj2(coding_lt_succ_cancel M N k)BN)HA)as BExA.
 exact(proj2(source_bounded_accept_unary M SFAll point out k(or_introl eq_refl)HO)
  (proj2(source_bounded_accept_binary M SFImpl member agr point(succM M k)(or_intror(or_intror eq_refl))HP)(conj BM BExA))).
Qed.
Theorem source_rec_exa_on_substitution M phi o a N old o' a' N' new rb rc rn base:
 source_bounded M phi(code_numeral M 2) ->source_rec_exa_on M phi o a N old ->source_rec_exa_on M phi o' a' N' new ->
 substitution_lookup M rb rc rn base o o' ->substitution_lookup M rb rc rn base a a' ->substitution_lookup M rb rc rn base N N' ->
 numerical_substitution M old rb rc rn base new.
Proof.
 intros BP(member&agr&point&HM&HA&HP&HO)(member'&agr'&point'&HM'&HA'&HP'&HO')HOO HAA HN.
 destruct(substitution_lift_total M rb rc rn base)as(lb&lc&ln&HL).
 apply(proj2(numerical_substitution_quantifier M true point old rb rc rn base new HO)). exists lb,lc,ln,point'.
 split;[exact HL|]. split;[|exact HO'].
 apply(proj2(numerical_substitution_binary M SFImpl member agr point lb lc ln(succM M base)point'(or_intror(or_intror eq_refl))HP)).
 exists member',agr'. split.
 - apply(proj2(numerical_substitution_member M _ _ member lb lc ln(succM M base)member' HM)).
   exists(zeroM M),(succM M N'). exact(conj(proj1(proj2 HL))(conj(proj2(proj2 HL)N N' HN)HM')).
 - split;[|exact HP']. exact(source_rec_exa_substitution M phi(zeroM M)(succM M o)(succM M a)(succM M N)agr
    (zeroM M)(succM M o')(succM M a')(succM M N')agr' lb lc ln(succM M base)BP HA HA'(proj1(proj2 HL))(proj2(proj2 HL)o o' HOO)(proj2(proj2 HL)a a' HAA)(proj2(proj2 HL)N N' HN)).
Qed.
Theorem source_rec_exa_on_shift M phi o a N old new:
 source_bounded M phi(code_numeral M 2) ->source_rec_exa_on M phi o a N old ->source_rec_exa_on M phi(succM M o)(succM M a)(succM M N)new ->source_formula_shift M old new.
Proof.
 intros BP HO HN. apply(proj2(numerical_renaming_substitution M old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new)).
 rewrite Arithmetic.add_zero. exact(source_rec_exa_on_substitution M phi o a N old(succM M o)(succM M a)(succM M N)new
  (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)BP HO HN(source_rec_shift_lookup M o)(source_rec_shift_lookup M a)(source_rec_shift_lookup M N)).
Qed.
Print Assumptions source_rec_exa_on_total.
Print Assumptions source_rec_exa_on_bounded.
Print Assumptions source_rec_exa_on_substitution.
Print Assumptions source_rec_exa_on_shift.
