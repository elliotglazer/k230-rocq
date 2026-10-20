(** Actual substitution and shift transport of the recursion hypotheses. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes NumericalSubstitutionMaps NumericalSubstitution
 NumericalRenaming RenamingSubstitution NumericalInstantiation SourceQuantifierRules SourceParameterTransport
 SourceRecursionPrimitiveRelations SourceRecursionPrimitiveTransport SourceRecursionShiftGraphs SourceRecursionInductionGraphs
 SourceRecursionSuccessorIn SourceRecursionAgreementSubset SourceFiniteParameters SourceFiniteNameParameters SourceInstantiationConstructors SourceTracePointRules SubstitutionSource.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Theorem source_rec_totality_substitution M N old N' new rb rc rn base:
 source_rec_totality M N old ->source_rec_totality M N' new ->substitution_lookup M rb rc rn base N N' ->
 numerical_substitution M old rb rc rn base new.
Proof.
 intros HO HN HLookup.
 apply(source_parameter_transport M 1 source_rec_totality_predicate source_rec_totality_finite_bound(source_finite_parameter_names 1)(source_finite_parameter_names 1)
  (fun _=>N)(fun _=>N')rb rc rn base old new);[|exact HO|exact HN].
 intros[|i]x y HI HX HY;[|lia]. change(x=N)in HX. change(y=N')in HY. now subst x y.
Qed.
Theorem source_rec_totality_shift M N old new:
 source_rec_totality M N old ->source_rec_totality M(succM M N)new ->source_formula_shift M old new.
Proof.
 intros HO HN. apply(proj2(numerical_renaming_substitution M old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new)).
 rewrite Arithmetic.add_zero. exact(source_rec_totality_substitution M N old(succM M N)new(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)HO HN(source_rec_shift_lookup M N)).
Qed.
Theorem source_rec_successor_in_shift M z X old new:
 source_rec_successor_in M z X old ->source_rec_successor_in M(succM M z)(succM M X)new ->source_formula_shift M old new.
Proof.
 intros HO HN. apply(proj2(numerical_renaming_substitution M old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new)).
 rewrite Arithmetic.add_zero. exact(source_rec_successor_in_substitution M z X old(succM M z)(succM M X)new(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)HO HN(source_rec_shift_lookup M z)(source_rec_shift_lookup M X)).
Qed.
Theorem source_rec_subset_chart_shift M f g N X old new:
 source_rec_subset_chart M f g N X old ->source_rec_subset_chart M(succM M f)(succM M g)(succM M N)(succM M X)new ->source_formula_shift M old new.
Proof.
 intros HO HN. apply(proj2(numerical_renaming_substitution M old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new)).
 rewrite Arithmetic.add_zero. exact(source_rec_subset_chart_substitution M f g N X old(succM M f)(succM M g)(succM M N)(succM M X)new(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)HO HN
  (source_rec_shift_lookup M f)(source_rec_shift_lookup M g)(source_rec_shift_lookup M N)(source_rec_shift_lookup M X)).
Qed.
Theorem source_rec_successor_body_instantiation M z X successor member body v succ' member' body':
 source_rec_successor M(succM M z)(zeroM M)successor ->sf_relation M SFMember(zeroM M)(succM M X)member ->
 sf_relation M SFAnd successor member body ->source_rec_successor M z v succ' ->sf_relation M SFMember v X member' ->
 sf_relation M SFAnd succ' member' body' ->numerical_instantiation M body v body'.
Proof.
 intros HS HM HB HS' HM' HB'.
 destruct(substitution_singleton_total M v)as(rb&rc&HHead&_).
 assert(IS:numerical_instantiation M successor v succ').
 { exists rb,rc. split;[exact HHead|]. exact(source_rec_successor_substitution M(succM M z)(zeroM M)successor z v succ' rb rc(code_numeral M 1)(zeroM M)HS HS'(substitution_singleton_tail M rb rc z)HHead). }
 exact(source_instantiation_binary M SFAnd successor member body v succ' member' body'(or_introl eq_refl)HB IS(source_instantiation_head_member M X member v member' HM HM')HB').
Qed.
Print Assumptions source_rec_totality_substitution.
Print Assumptions source_rec_totality_shift.
Print Assumptions source_rec_successor_in_shift.
Print Assumptions source_rec_subset_chart_shift.
Print Assumptions source_rec_successor_body_instantiation.
