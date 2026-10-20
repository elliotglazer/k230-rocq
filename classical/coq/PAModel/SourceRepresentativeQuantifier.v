(** An auxiliary representative may be closed at its own high name.
    This gives exactly the same quantified formula as closing the original
    representative0, when the auxiliary name lies outside the source bound. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 NumericalRenamingMaps NumericalRenaming SourceRenamingIdentity SourceRenamingDiamond
 RawBinderRenaming SourceRepresentativeRenaming SourceNamedQuantifierRules SourceShiftSpecialization NumericalEnvironments.
Unset Implicit Arguments.

Theorem source_representative_quantifier_normalization M universal f g r k quantified original :
 source_bounded M f k ->~coding_lt M r k ->source_representative_renaming M r f g ->
 source_named_quantifier M universal r g quantified ->
 source_named_quantifier M universal(zeroM M)f original ->quantified=original.
Proof.
 intros HF HR HG(rb&rc&body&HM&HBody&HQuant)(sb&sc&first&HS&HFirst&HOriginal).
 assert(HId:numerical_renaming M f(zeroM M)(zeroM M)(zeroM M)(zeroM M)f).
 { apply(numerical_renaming_identity_on_bound M f _ _ _ _ k HF).
   intros i _. apply source_empty_renaming_lookup. }
 assert(HClose:numerical_renaming M g rb rc(succM M r)(code_numeral M 1)first).
 { apply(numerical_source_renaming_diamond M f k
    (zeroM M)(zeroM M)(zeroM M)(zeroM M)
    r r(code_numeral M 1)(zeroM M)
    sb sc(succM M(zeroM M))(code_numeral M 1)
    rb rc(succM M r)(code_numeral M 1) f g first HF HId HG HFirst).
   intros i j l m HI HJ HM0 HRep.
   rewrite(renaming_lookup_functional M _ _ _ _ i j i HJ(source_empty_renaming_lookup M i))in HM0.
   assert(HDecision:i=zeroM M \/i<>zeroM M).
   { destruct(environment_lt_cases M i(code_numeral M 1))as[HL|HN].
     - apply coding_lt_succ_cases in HL. destruct HL as[HB|E];[exfalso;exact(coding_not_lt_zero M i HB)|now left].
     - right. intro E. subst i. exact(HN(coding_zero_lt_succ M(zeroM M))). }
   destruct HDecision as[->|HN].
   - rewrite(renaming_lookup_functional M _ _ _ _ _ l r HRep(representative_lookup_zero M r)).
     apply(proj1(HS(zeroM M)m))in HM0. destruct HM0 as[[_ ->]|[H _]];[|contradiction].
     apply(proj2(HM r(zeroM M))). now left.
   - rewrite(renaming_lookup_functional M _ _ _ _ i l i HRep(representative_lookup_nonzero M r i HN)).
     apply(proj1(HS i m))in HM0. destruct HM0 as[[H _]|[_ ->]];[contradiction|].
     apply(proj2(HM i(succM M i))). right. split;[|reflexivity].
     intro E. subst i. exact(HR HI). }
 rewrite(numerical_renaming_functional M g rb rc _ _ body first HBody HClose)in HQuant.
 exact(sf_relation_functional M _ first(zeroM M) quantified original HQuant HOriginal).
Qed.

Theorem source_representative_quantifier_bound M universal f g r k quantified :
 source_bounded M f k ->~coding_lt M r k ->source_representative_renaming M r f g ->
 source_named_quantifier M universal r g quantified ->source_bounded M quantified k.
Proof.
 intros HF HR HG HQ.
 destruct(source_named_quantifier_total M universal(zeroM M)f)as(original&HO).
 rewrite(source_representative_quantifier_normalization M universal f g r k quantified original HF HR HG HQ HO).
 exact(source_named_quantifier_bound M universal(zeroM M)f original k HF HO).
Qed.

Print Assumptions source_representative_quantifier_normalization.
Print Assumptions source_representative_quantifier_bound.
