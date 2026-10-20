(** Agreement at every index of a named recursion domain. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 NumericalSubstitutionMaps NumericalSubstitution NumericalRenaming RenamingSubstitution SourceQuantifierRules
 SourceRecursionPrimitiveRelations SourceRecursionAgreement SourceRecursionShiftGraphs.
Unset Implicit Arguments.
Definition source_rec_agrees_on M f g N out:=exists member agr point,
 sf_relation M SFMember(zeroM M)(succM M N)member /\source_rec_agreement M(succM M f)(succM M g)(zeroM M)agr /\
 sf_relation M SFImpl member agr point /\sf_relation M SFAll point(zeroM M)out.
Theorem source_rec_agrees_on_total M f g N:exists out,source_rec_agrees_on M f g N out.
Proof.
 destruct(sf_relation_total M SFMember(zeroM M)(succM M N))as(member&HM).
 destruct(source_rec_agreement_total M(succM M f)(succM M g)(zeroM M))as(agr&HA).
 destruct(sf_relation_total M SFImpl member agr)as(point&HP).
 destruct(sf_relation_total M SFAll point(zeroM M))as(out&HO). exists out,member,agr,point. auto.
Qed.
Theorem source_rec_agrees_on_bounded M f g N out k:
 coding_lt M f k ->coding_lt M g k ->coding_lt M N k ->source_rec_agrees_on M f g N out ->source_bounded M out k.
Proof.
 intros BF BG BN(member&agr&point&HM&HA&HP&HO).
 assert(BM:source_bounded M member(succM M k))by exact(proj2(source_bounded_accept_atom M SFMember _ _ member(succM M k)(or_introl eq_refl)HM)
  (conj(coding_zero_lt_succ M k)(proj2(coding_lt_succ_cancel M N k)BN))).
 pose proof(source_rec_agreement_bounded M(succM M f)(succM M g)(zeroM M)agr(succM M k)
  (proj2(coding_lt_succ_cancel M f k)BF)(proj2(coding_lt_succ_cancel M g k)BG)(coding_zero_lt_succ M k)HA)as BA.
 exact(proj2(source_bounded_accept_unary M SFAll point out k(or_introl eq_refl)HO)
  (proj2(source_bounded_accept_binary M SFImpl member agr point(succM M k)(or_intror(or_intror eq_refl))HP)(conj BM BA))).
Qed.
Theorem source_rec_agrees_on_substitution M f g N old f' g' N' new rb rc rn base:
 source_rec_agrees_on M f g N old ->source_rec_agrees_on M f' g' N' new ->
 substitution_lookup M rb rc rn base f f' ->substitution_lookup M rb rc rn base g g' ->substitution_lookup M rb rc rn base N N' ->
 numerical_substitution M old rb rc rn base new.
Proof.
 intros(member&agr&point&HM&HA&HP&HO)(member'&agr'&point'&HM'&HA'&HP'&HO')HF HG HN.
 destruct(substitution_lift_total M rb rc rn base)as(lb&lc&ln&HL).
 apply(proj2(numerical_substitution_quantifier M true point old rb rc rn base new HO)). exists lb,lc,ln,point'.
 split;[exact HL|]. split;[|exact HO'].
 apply(proj2(numerical_substitution_binary M SFImpl member agr point lb lc ln(succM M base)point'(or_intror(or_intror eq_refl))HP)).
 exists member',agr'. split.
 - apply(proj2(numerical_substitution_member M _ _ member lb lc ln(succM M base)member' HM)).
   exists(zeroM M),(succM M N'). exact(conj(proj1(proj2 HL))(conj(proj2(proj2 HL)N N' HN)HM')).
 - split;[|exact HP']. exact(source_rec_agreement_substitution M(succM M f)(succM M g)(zeroM M)agr
    (succM M f')(succM M g')(zeroM M)agr' lb lc ln(succM M base)HA HA'(proj2(proj2 HL)f f' HF)(proj2(proj2 HL)g g' HG)(proj1(proj2 HL))).
Qed.
Theorem source_rec_agrees_on_shift M f g N old new:
 source_rec_agrees_on M f g N old ->source_rec_agrees_on M(succM M f)(succM M g)(succM M N)new ->source_formula_shift M old new.
Proof.
 intros HO HN. apply(proj2(numerical_renaming_substitution M old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new)).
 rewrite Arithmetic.add_zero. exact(source_rec_agrees_on_substitution M f g N old(succM M f)(succM M g)(succM M N)new
  (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)HO HN(source_rec_shift_lookup M f)(source_rec_shift_lookup M g)(source_rec_shift_lookup M N)).
Qed.
Print Assumptions source_rec_agrees_on_total.
Print Assumptions source_rec_agrees_on_bounded.
Print Assumptions source_rec_agrees_on_substitution.
Print Assumptions source_rec_agrees_on_shift.
