(** The falsity branch of the representation invariant, for arbitrary
    internal assignment length. This is a pure source logical theorem. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
 SourceBounded SourceBoundMonotone SourceBoundedCalibration SourceNumeralLift SourceQuantifierRules SourceDefinabilityPrimitives
 SourceDefinabilityBounds SourceFiniteCutoffShift SourceRepresentationRecipe SourceRepresentationFalsityPoint
 SourceDnConditionalStep SourceDnConditionalIntroduction SourceDn SourceDescriptorProvability
 NumericalRenaming SourceSetRelativizationFunctionality SourceSetRelativization
 SetSchemaConstructors SchemaConstructorBounds SourceRelativizationRules.
Unset Implicit Arguments.

Lemma representation_falsity_iff_any_environment M rho false_expression :
 code_relation M rho false_expression(zeroM M) ->code_relation M rho
 (E_sf_iff(E_sf SFMember(CEconst 0)(CEconst 1)) false_expression)
 (code_numeral M(sf_encode representation_falsity_iff)).
Proof.
 intro HFalse.
 assert(HA:code_relation M rho(E_sf SFMember(CEconst 0)(CEconst 1))
   (code_numeral M(sf_make SFMember 0 1))).
 { exact(proj2(schema_expression_graph M rho SFMember(CEconst 0)(CEconst 1)
   (zeroM M)(code_numeral M 1)(code_numeral M(sf_make SFMember 0 1)) eq_refl eq_refl)
   (sf_make_numeral M SFMember 0 1)). }
 assert(HL:code_relation M rho(E_sf SFImpl(E_sf SFMember(CEconst 0)(CEconst 1)) false_expression)
   (code_numeral M(sf_make SFImpl(sf_make SFMember 0 1) 0))).
 { exact(proj2(schema_expression_graph M rho SFImpl(E_sf SFMember(CEconst 0)(CEconst 1)) false_expression
    (code_numeral M(sf_make SFMember 0 1))(zeroM M)
    (code_numeral M(sf_make SFImpl(sf_make SFMember 0 1) 0)) HA HFalse)
    (sf_make_numeral M SFImpl(sf_make SFMember 0 1) 0)). }
 assert(HR:code_relation M rho(E_sf SFImpl false_expression(E_sf SFMember(CEconst 0)(CEconst 1)))
   (code_numeral M(sf_make SFImpl 0(sf_make SFMember 0 1)))).
 { exact(proj2(schema_expression_graph M rho SFImpl false_expression(E_sf SFMember(CEconst 0)(CEconst 1))
    (zeroM M)(code_numeral M(sf_make SFMember 0 1))
    (code_numeral M(sf_make SFImpl 0(sf_make SFMember 0 1))) HFalse HA)
    (sf_make_numeral M SFImpl 0(sf_make SFMember 0 1))). }
 exact(proj2(schema_expression_graph M rho SFAnd _ _ _ _ _ HL HR)
   (sf_make_numeral M SFAnd(sf_make SFImpl(sf_make SFMember 0 1) 0)
    (sf_make SFImpl 0(sf_make SFMember 0 1)))).
Qed.

Theorem source_descriptor_representation_falsity M T n result out :
 source_representation_recipe M n(zeroM M) result ->
 sf_relation M SFImpl(code_numeral M(sf_encode source_def_empty)) result out ->
 source_descriptor_provable M T out.
Proof.
 intros(env&first&shifted&matrix&relative&body&HE&H1&H2&HM&HR&HB&HD) HO.
 apply(proj1(numerical_renaming_invalid M(zeroM M)(zeroM M)(zeroM M)(zeroM M)
   (code_numeral M 3) matrix(or_introl eq_refl)))in HM. subst matrix.
 pose proof(source_set_relativization_invalid_inv M(code_numeral M 2)(zeroM M) relative
   (or_introl eq_refl) HR)as E. subst relative.
 pose proof(source_cutoff_shift_bounded M 1 env first n(source_envf_bound M n env HE) H1)as BFirst.
 pose proof(source_cutoff_shift_bounded M 1 first shifted(succM M n) BFirst H2)as BShifted.
 set(iffcode:=code_numeral M(sf_encode representation_falsity_iff)).
 destruct(sf_relation_total M SFImpl shifted iffcode)as(guarded&HGuard).
 destruct(sf_relation_total M SFAll guarded(zeroM M))as(body'&HAll).
 assert(HBody:code_relation M(representation_point_environment shifted(zeroM M))
   (E_representation_point(CEvar 0)(CEvar 1)) body').
 { unfold E_representation_point.
   pose proof(representation_falsity_iff_any_environment M
    (representation_point_environment shifted(zeroM M))(CEvar 1) eq_refl)as HIff.
   pose proof(proj2(schema_expression_graph M _ SFImpl(CEvar 0) _ shifted iffcode guarded eq_refl HIff) HGuard)as HGuarded.
   exact(proj2(schema_expression_graph M _ SFAll _ (CEconst 0) guarded(zeroM M) body' HGuarded eq_refl) HAll). }
 rewrite(code_relation_functional M _ _ body body' HB HBody)in HD.
 assert(BIff:source_bounded M iffcode(succM M(succM M(succM M n)))).
 { apply(source_bounded_monotone M iffcode(code_numeral M 2)(succM M(succM M(succM M n)))).
   - assert(B:schema_expression_bound M(fun _=>zeroM M)
      (E_sf_iff(E_sf SFMember(CEconst 0)(CEconst 1))(CEconst 0))(code_numeral M 2)).
     { unfold E_sf_iff. repeat schema_constructor_bound;try schema_small_index;apply source_bounded_accept_falsity. }
     exact(B iffcode(representation_falsity_iff_any_environment M(fun _=>zeroM M)(CEconst 0) eq_refl)).
   - do 2 apply coding_lt_succ_cancel. apply coding_zero_lt_succ. }
 destruct(sf_relation_total M SFImpl(code_numeral M(sf_encode representation_empty_shift)) iffcode)as(point&HPoint).
 destruct(sf_relation_total M SFImpl(code_numeral M(sf_encode source_def_empty)) body')as(bodyPoint&HBodyPoint).
 assert(PBody:source_descriptor_provable M T bodyPoint).
 { apply(source_descriptor_conditional_guarded_all_intro M T
    (code_numeral M(sf_encode source_def_empty))(code_numeral M(sf_encode representation_empty_shift))
    iffcode shifted point guarded body' bodyPoint(succM M(succM M n))).
   - apply(source_bounded_monotone M _(code_numeral M 1)(succM M(succM M n))(numerical_def_empty_bound M)).
     apply coding_lt_succ_cancel,coding_zero_lt_succ.
   - exact BIff.
   - exact BShifted.
   - exact(representation_empty_shift_graph M).
   - exact HPoint.
   - exact HGuard.
   - exact HAll.
   - exact HBodyPoint.
   - exact(source_descriptor_representation_falsity_point M T point HPoint). }
 assert(BBody:source_bounded M body'(addM M n(code_numeral M 2))).
 { rewrite Arithmetic.add_comm. change(source_bounded M body'(addM M(succM M(succM M(zeroM M))) n)).
   rewrite !Arithmetic.add_succ,Arithmetic.add_zero.
   apply(proj2(source_bounded_accept_unary M SFAll guarded body'(succM M(succM M n))(or_introl eq_refl) HAll)).
   exact(proj2(source_bounded_accept_binary M SFImpl shifted iffcode guarded(succM M(succM M(succM M n)))
    (or_intror(or_intror eq_refl)) HGuard)(conj BShifted BIff)). }
 apply(source_descriptor_dn_conditional_intro M T n(code_numeral M(sf_encode source_def_empty)) body'
   result(zeroM M) bodyPoint out);try assumption.
 apply(source_bounded_monotone M _(code_numeral M 1)(code_numeral M 2)(numerical_def_empty_bound M)).
 apply coding_lt_succ_cancel,coding_zero_lt_succ.
Qed.
Print Assumptions representation_falsity_iff_any_environment.
Print Assumptions source_descriptor_representation_falsity.
