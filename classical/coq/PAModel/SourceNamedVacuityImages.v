(** Name vacuity is preserved when an actual bounded source renaming
    avoids that name throughout its image. This applies to arbitrary
    internal formulas, including formulas with repeated bound names. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SourceBounded
 NumericalRenamingMaps NumericalRenaming NumericalContextRenaming SourceRenamingDiamond SourceQuantifierRules
 SourceNamedVacuity RawBinderRenaming SourceRepresentativeRenaming SourceNumeralLift.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Theorem source_named_vacuous_renaming_image M f g k b c n delta x :
 source_bounded M f k ->numerical_renaming M f b c n delta g ->
 (forall i j,coding_lt M i k ->renaming_lookup M b c n delta i j ->j<>x) ->source_named_vacuous M x g.
Proof.
 intros HF HG HImage rb rc closed shifted HM HC HS.
 assert(HShift:source_formula_shift M g closed).
 { apply(numerical_source_renaming_diamond M f k b c n delta b c n delta
    rb rc(succM M x)(code_numeral M 1)
    (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1) g g closed HF HG HG HC).
   intros i j l m HI HJ HJM HL.
   assert(E:l=j)by(eapply renaming_lookup_functional;eassumption). subst l.
   apply(proj1(HM j m))in HJM. destruct HJM as[[E _]|[_ E]].
   - exfalso. exact(HImage i j HI HJ E).
   - apply(proj2(context_shift_lookup M j m)). exact E. }
 exact(numerical_renaming_functional M g _ _ _ _ closed shifted HShift HS).
Qed.
Theorem source_named_vacuous_representative_image M f g r x :
 source_bounded M f(code_numeral M 2) ->source_representative_renaming M r f g ->
 r<>x ->code_numeral M 1<>x ->source_named_vacuous M x g.
Proof.
 intros HF HG HR HOne. apply(source_named_vacuous_renaming_image M f g(code_numeral M 2)
   r r(code_numeral M 1)(zeroM M)x HF HG).
 intros i j HI HJ. destruct(source_numeral_initial_segment M 2 i HI)as(index&HIndex&->).
 destruct index as[|[|index]];try lia.
 - rewrite(renaming_lookup_functional M _ _ _ _ _ j r HJ(representative_lookup_zero M r)). exact HR.
 - assert(HNZ:code_numeral M 1<>zeroM M).
   { intro E. exact(Model.zero_ne_succ M(zeroM M)(eq_sym E)). }
   rewrite(renaming_lookup_functional M _ _ _ _ _ j(code_numeral M 1) HJ(representative_lookup_nonzero M r _ HNZ)). exact HOne.
Qed.
Print Assumptions source_named_vacuous_renaming_image.
Print Assumptions source_named_vacuous_representative_image.
