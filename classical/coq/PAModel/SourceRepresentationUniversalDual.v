(** Literal universal/negative-existential representation comparison,
    for arbitrary internal source matrices and arbitrary assignment count. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SetSchemaConstructors SchemaConstructorBounds SourceBounded FixedSourceBounds SourceNumeralLift
 SourceRepresentationRecipe SourceRepresentationPointDataBound SourceRepresentationPointEquivalence SourceGuardedDualityImplications
 SourceQuantifierMatrixScopes SourceExistentialRecipe SourceSetRelativization SourceSetRelativizationRules SourceSetRelativizationFunctionality SourceSetRelativizationBounds
 SourceFiniteCutoffShift SourceDefinabilityBounds SourceRenamingBounds NumericalRenamingMaps NumericalRenaming
 SourceDn SourceDnProofMap SourceDescriptorProvability SourceDescriptorClosure SourceSetTheoryDescriptors SourceZFRProvability.
From FOL.Tennenbaum Require Peano.
Unset Implicit Arguments.
Theorem source_zfr_representation_universal_dual M count f universal rep:
 source_bounded M universal count->sf_relation M SFAll f(zeroM M)universal->source_representation_recipe M count universal rep->
 exists negf exneg negative negativeRep law,
 sf_relation M SFImpl f(zeroM M)negf/\sf_relation M SFEx negf(zeroM M)exneg/\sf_relation M SFImpl exneg(zeroM M)negative/\
 source_bounded M negative count/\source_representation_recipe M count negative negativeRep/\
 sf_relation M SFImpl negativeRep rep law/\source_zfr_provable M law.
Proof.
 intros BAll HAll(environment&first&guard&matrix&relative&point&HE&H1&H2&HMatrix&HRelative&HPoint&HDPoint).
 pose proof(proj1(source_bounded_accept_unary M SFAll f universal count(or_introl eq_refl)HAll)BAll)as BF.
 destruct(proj1(numerical_renaming_quantifier M true f universal(zeroM M)(zeroM M)(zeroM M)(code_numeral M 3)matrix HAll)HMatrix)
  as(b&c&n&matrixF&HL&HMatrixF&HAllMatrix).
 pose proof(proj1(numerical_renaming_extensional M f b c n(zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M 3)matrixF
  (source_empty_three_lift_equivalent M b c n HL))HMatrixF)as HOneRole.
 destruct(source_set_relativization_quantifier_inv M(code_numeral M 2)true matrixF matrix relative HAllMatrix HRelative)
  as(relativeF&HRelativeF&member&guarded&HMember&HGuarded&HAllRelative).
 destruct(sf_relation_total M SFImpl f(zeroM M))as(negf&HNegF).
 destruct(sf_relation_total M SFEx negf(zeroM M))as(exneg&HExNeg).
 destruct(sf_relation_total M SFImpl exneg(zeroM M))as(negative&HNegative).
 destruct(sf_relation_total M SFImpl matrixF(zeroM M))as(matrixNegF&HMatrixNegF).
 destruct(sf_relation_total M SFEx matrixNegF(zeroM M))as(matrixExNeg&HMatrixExNeg).
 destruct(sf_relation_total M SFImpl matrixExNeg(zeroM M))as(matrixNegative&HMatrixNegative).
 assert(HMapNegF:numerical_renaming M negf b c n(code_numeral M 3)matrixNegF).
 { apply(proj2(numerical_renaming_binary M SFImpl f(zeroM M)negf b c n(code_numeral M 3)matrixNegF(or_intror(or_intror eq_refl))HNegF)).
   exists matrixF,(zeroM M). exact(conj HMatrixF(conj(proj2(numerical_renaming_invalid M(zeroM M)b c n(code_numeral M 3)(zeroM M)(or_introl eq_refl))eq_refl)HMatrixNegF)). }
 assert(HMapExNeg:numerical_renaming M exneg(zeroM M)(zeroM M)(zeroM M)(code_numeral M 3)matrixExNeg).
 { apply(proj2(numerical_renaming_quantifier M false negf exneg(zeroM M)(zeroM M)(zeroM M)(code_numeral M 3)matrixExNeg HExNeg)).
   exists b,c,n,matrixNegF. exact(conj HL(conj HMapNegF HMatrixExNeg)). }
 assert(HMapNegative:numerical_renaming M negative(zeroM M)(zeroM M)(zeroM M)(code_numeral M 3)matrixNegative).
 { apply(proj2(numerical_renaming_binary M SFImpl exneg(zeroM M)negative(zeroM M)(zeroM M)(zeroM M)(code_numeral M 3)matrixNegative(or_intror(or_intror eq_refl))HNegative)).
   exists matrixExNeg,(zeroM M). exact(conj HMapExNeg(conj(proj2(numerical_renaming_invalid M(zeroM M)(zeroM M)(zeroM M)(zeroM M)(code_numeral M 3)(zeroM M)(or_introl eq_refl))eq_refl)HMatrixNegative)). }
 destruct(sf_relation_total M SFImpl relativeF(zeroM M))as(relativeNegF&HRelativeNegF).
 destruct(sf_relation_total M SFAnd member relativeNegF)as(both&HBoth).
 destruct(sf_relation_total M SFEx both(zeroM M))as(exBoth&HExBoth).
 destruct(sf_relation_total M SFImpl exBoth(zeroM M))as(notBoth&HNotBoth).
 pose proof(source_set_relativization_binary M(code_numeral M 3)SFImpl matrixF(zeroM M)matrixNegF relativeF(zeroM M)relativeNegF
  (or_intror(or_intror eq_refl))HMatrixNegF HRelativeF(source_set_relativization_falsity M(code_numeral M 3))HRelativeNegF)as HRelNegF.
 assert(HRelExNeg:source_set_relativization M(code_numeral M 2)matrixExNeg exBoth).
 { apply(source_set_relativization_quantifier M(code_numeral M 2)false matrixNegF matrixExNeg relativeNegF exBoth HMatrixExNeg HRelNegF).
   exists member,both. exact(conj HMember(conj HBoth HExBoth)). }
 pose proof(source_set_relativization_binary M(code_numeral M 2)SFImpl matrixExNeg(zeroM M)matrixNegative exBoth(zeroM M)notBoth
  (or_intror(or_intror eq_refl))HMatrixNegative HRelExNeg(source_set_relativization_falsity M(code_numeral M 2))HNotBoth)as HRelNegative.
 destruct(code_relation_total M(E_representation_point(CEvar 0)(CEvar 1))(representation_point_environment guard notBoth))as(negativePoint&HNegativePoint).
 destruct(source_dn_total M count negativePoint)as(negativeRep&HDNegative).
 assert(HNegativeRep:source_representation_recipe M count negative negativeRep).
 { exists environment,first,guard,matrixNegative,notBoth,negativePoint. exact(conj HE(conj H1(conj H2(conj HMapNegative(conj HRelNegative(conj HNegativePoint HDNegative)))))). }
 assert(BNegF:source_bounded M negf(succM M count)).
 { exact(proj2(source_bounded_accept_binary M SFImpl f(zeroM M)negf _(or_intror(or_intror eq_refl))HNegF)(conj BF(source_bounded_accept_falsity M _))). }
 pose proof(proj2(source_bounded_accept_unary M SFEx negf exneg count(or_intror eq_refl)HExNeg)BNegF)as BExNeg.
 assert(BNegative:source_bounded M negative count).
 { exact(proj2(source_bounded_accept_binary M SFImpl exneg(zeroM M)negative count(or_intror(or_intror eq_refl))HNegative)(conj BExNeg(source_bounded_accept_falsity M _))). }
 set(k:=succM M(succM M(succM M count))).
 assert(BMatrixF:source_bounded M matrixF(succM M k)).
 { apply(numerical_renaming_preserves_bound M f(zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M 3)matrixF(succM M count)(succM M k)BF HOneRole).
   intros i j HI HJ. destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)as[->|[v ->]].
   - rewrite(renaming_lookup_functional M _ _ _ _ _ j _ HJ(source_one_role_zero_lookup M(zeroM M)(code_numeral M 3))). apply coding_zero_lt_succ.
   - assert(HN:succM M v<>zeroM M)by(exact(fun E=>Model.zero_ne_succ M v(eq_sym E))).
     rewrite(renaming_lookup_functional M _ _ _ _ _ j _ HJ(source_one_role_positive_lookup M(zeroM M)(code_numeral M 3)_ HN)).
     rewrite Arithmetic.add_comm. cbn[code_numeral]. rewrite!Arithmetic.add_succ,Arithmetic.add_zero.
     do 3 apply coding_lt_succ_cancel. exact HI. }
 assert(H3:coding_lt M(code_numeral M 3)(succM M k)).
 { change(coding_lt M(succM M(succM M(succM M(zeroM M))))(succM M(succM M(succM M(succM M count))))).
   do 3 apply coding_lt_succ_cancel. apply coding_zero_lt_succ. }
 pose proof(source_set_relativization_preserves_bound M matrixF(code_numeral M 3)(succM M k)relativeF H3 BMatrixF HRelativeF)as BRelativeF.
 assert(BMember:source_bounded M member(succM M k)).
 { exact(proj2(source_bounded_accept_atom M SFMember(zeroM M)(code_numeral M 3)member _(or_introl eq_refl)HMember)(conj(coding_zero_lt_succ M _)H3)). }
 destruct(sf_relation_total M SFImpl notBoth relative)as(forward&HForward).
 destruct(sf_relation_total M SFImpl relative notBoth)as(reverse&HReverse).
 destruct(source_guarded_duality_empty M member relativeF guarded relativeNegF both exBoth notBoth relative forward reverse k
  BMember BRelativeF HGuarded HRelativeNegF HBoth HExBoth HNotBoth HAllRelative HForward HReverse)as[PF PR].
 assert(BRelative:source_bounded M relative k).
 { apply(proj2(source_bounded_accept_unary M SFAll guarded relative k(or_introl eq_refl)HAllRelative)).
   exact(proj2(source_bounded_accept_binary M SFImpl member relativeF guarded _(or_intror(or_intror eq_refl))HGuarded)(conj BMember BRelativeF)). }
 assert(BRelNeg:source_bounded M notBoth k).
 { apply(proj2(source_bounded_accept_binary M SFImpl exBoth(zeroM M)notBoth k(or_intror(or_intror eq_refl))HNotBoth)).
   split;[|apply source_bounded_accept_falsity]. apply(proj2(source_bounded_accept_unary M SFEx both exBoth k(or_intror eq_refl)HExBoth)).
   apply(proj2(source_bounded_accept_binary M SFAnd member relativeNegF both _(or_introl eq_refl)HBoth)). split;[exact BMember|].
   exact(proj2(source_bounded_accept_binary M SFImpl relativeF(zeroM M)relativeNegF _(or_intror(or_intror eq_refl))HRelativeNegF)(conj BRelativeF(source_bounded_accept_falsity M _))). }
 pose proof(source_cutoff_shift_bounded M 1 environment first count(source_envf_bound M count environment HE)H1)as BFirst.
 pose proof(source_cutoff_shift_bounded M 1 first guard(succM M count)BFirst H2)as BGuard.
 pose proof(source_representation_point_data_bound M count universal environment first guard matrix relative point BAll HE H1 H2 HMatrix HRelative HPoint)as BPoint.
 assert(BNegativePoint:source_bounded M negativePoint(succM M(succM M count))).
 { assert(B:schema_expression_bound M(representation_point_environment guard notBoth)(E_representation_point(CEvar 0)(CEvar 1))(succM M(succM M count))).
   { unfold E_representation_point,E_sf_iff. repeat schema_constructor_bound;try schema_small_index;assumption. }
   exact(B negativePoint HNegativePoint). }
 destruct(sf_relation_total M SFImpl negativePoint point)as(pointLaw&HPointLaw).
 pose proof(source_descriptor_representation_point_equivalence M ZFRSourceDescriptor guard notBoth relative negativePoint point forward reverse pointLaw k
  BGuard BRelNeg BRelative(coding_zero_lt_succ M _)
  ltac:(change(coding_lt M(succM M(zeroM M))(succM M(succM M(succM M count))));apply coding_lt_succ_cancel,coding_zero_lt_succ)
  HNegativePoint HPoint HForward HReverse(source_descriptor_provable_from_empty M ZFRSourceDescriptor forward PF)(source_descriptor_provable_from_empty M ZFRSourceDescriptor reverse PR)HPointLaw)as PPointLaw.
 destruct(sf_relation_total M SFImpl negativeRep rep)as(law&HLaw).
 assert(BP:source_bounded M point(addM M count(succM M(succM M(zeroM M))))).
 { rewrite Arithmetic.add_comm,!Arithmetic.add_succ,Arithmetic.add_zero. exact BPoint. }
 assert(BNP:source_bounded M negativePoint(addM M count(succM M(succM M(zeroM M))))).
 { rewrite Arithmetic.add_comm,!Arithmetic.add_succ,Arithmetic.add_zero. exact BNegativePoint. }
 pose proof(source_descriptor_dn_map M ZFRSourceDescriptor count negativePoint point negativeRep rep(zeroM M)pointLaw law BNP BP HDNegative HDPoint HPointLaw HLaw PPointLaw)as PLaw.
 exists negf,exneg,negative,negativeRep,law.
 exact(conj HNegF(conj HExNeg(conj HNegative(conj BNegative(conj HNegativeRep(conj HLaw(proj1(source_zfr_descriptor_provable M law)PLaw))))))).
Qed.
Print Assumptions source_zfr_representation_universal_dual.
