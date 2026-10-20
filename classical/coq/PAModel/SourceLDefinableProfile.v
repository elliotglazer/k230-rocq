(** The exact canonical conclusion of pinned Z_axL.L_definable.
    This module constructs syntax uniformly for arbitrary internal matrices;
    it does not assume or prove the still-needed definability certificate. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions NumericalProofs SetFormulaCodes
 SourceNumeralLift SourceBounded SourceBoundMonotone SourceLFixed SourceFiniteCutoffShift
 SourceQfFunctionality SourceSetRelativization SourceSetRelativizationFunctionality
 SourceSetRelativizationBounds SetSchemaConstructors SchemaConstructorBounds.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
Definition E_L_definable_profile matrix memberL :=E_sf SFEx
 (E_sf SFAnd memberL(E_sf SFAll
  (E_sf_iff(E_sf SFMember(CEconst 0)(CEconst 1))
   (E_sf SFAnd(E_sf SFMember(CEconst 0)(CEconst 2)) matrix))(CEconst 0)))(CEconst 0).
Definition L_definable_profile_environment {A}(matrix memberL:A) i :=match i with 0=>matrix|_=>memberL end.
Definition source_definable_profile M domain phi result :=exists first matrix relative,
 source_cutoff_shift M 1 phi first /\source_cutoff_shift M 1 first matrix /\
 source_set_relativization M(code_numeral M 2) matrix relative /\
 code_relation M(L_definable_profile_environment relative domain)
   (E_L_definable_profile(CEvar 0)(CEvar 1)) result.
Definition source_definable_profile_formula(domain phi result:term):form :=∃∃∃(
 source_cutoff_shift_formula 1(lift3 phi) $2 ∧
 (source_cutoff_shift_formula 1 $2 $1 ∧
 (source_set_relativization_formula(num 2) $1 $0 ∧
 code_formula(E_L_definable_profile(CEvar 0)(CEvar 1))
  (L_definable_profile_environment $0(lift3 domain))(lift3 result)))).
Local Opaque holds source_cutoff_shift_formula source_set_relativization_formula code_formula code_relation source_L_domain_code.
Theorem source_definable_profile_formula_correct M rho domain phi result :
 holds M rho(source_definable_profile_formula domain phi result) <->
 source_definable_profile M(evalM M rho domain)(evalM M rho phi)(evalM M rho result).
Proof.
 unfold source_definable_profile_formula,source_definable_profile.
 repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
 setoid_rewrite source_cutoff_shift_formula_correct.
 setoid_rewrite source_set_relativization_formula_correct.
 setoid_rewrite code_formula_correct. repeat setoid_rewrite code_eval_num.
 unfold evalM,lift3. repeat setoid_rewrite eval_up.
 split;intros(first&matrix&relative&H1&H2&HR&HO);exists first,matrix,relative;
   refine(conj H1(conj H2(conj HR _))).
 - apply(proj1(code_relation_ext M(E_L_definable_profile(CEvar 0)(CEvar 1))
     (fun index => evalM M (relative .: matrix .: first .: rho) (L_definable_profile_environment $0 (lift3 domain) index))
     (L_definable_profile_environment relative(evalM M rho domain)) (evalM M rho result)
     ltac:(intros[|i];[reflexivity|unfold L_definable_profile_environment,evalM,lift3;repeat rewrite eval_up;reflexivity]))). exact HO.
 - apply(proj2(code_relation_ext M(E_L_definable_profile(CEvar 0)(CEvar 1))
     (fun index => evalM M (relative .: matrix .: first .: rho) (L_definable_profile_environment $0 (lift3 domain) index))
     (L_definable_profile_environment relative(evalM M rho domain)) (evalM M rho result)
     ltac:(intros[|i];[reflexivity|unfold L_definable_profile_environment,evalM,lift3;repeat rewrite eval_up;reflexivity]))). exact HO.
Qed.
Theorem source_definable_profile_total M domain phi :exists result,source_definable_profile M domain phi result.
Proof.
 destruct(source_cutoff_shift_total M 1 phi)as(first&H1).
 destruct(source_cutoff_shift_total M 1 first)as(matrix&H2).
 destruct(source_set_relativization_total M(code_numeral M 2) matrix)as(relative&HR).
 destruct(code_relation_total M(E_L_definable_profile(CEvar 0)(CEvar 1))
   (L_definable_profile_environment relative domain))as(result&HO).
 exists result,first,matrix,relative. auto.
Qed.
Theorem source_definable_profile_functional M domain phi result other :
 source_definable_profile M domain phi result ->source_definable_profile M domain phi other ->result=other.
Proof.
 intros(a&b&r&H1&H2&HR&HO)(a'&b'&r'&H1'&H2'&HR'&HP).
 assert(a=a')by(eapply source_cutoff_shift_functional;eassumption). subst a'.
 assert(b=b')by(eapply source_cutoff_shift_functional;eassumption). subst b'.
 assert(r=r')by(eapply source_set_relativization_functional;eassumption). subst r'.
 eapply code_relation_functional;eassumption.
Qed.
Theorem source_definable_profile_bounded M domain m phi result :
 source_bounded M domain(code_numeral M 1) ->
 source_bounded M phi(succM M m) ->source_definable_profile M domain phi result ->
 source_bounded M result(succM M m).
Proof.
 intros HD HP(first&matrix&relative&H1&H2&HR&HO).
 pose proof(source_cutoff_shift_bounded M 1 phi first m HP H1)as B1.
 pose proof(source_cutoff_shift_bounded M 1 first matrix(succM M m) B1 H2)as B2.
 assert(BR:source_bounded M relative(succM M(succM M(succM M m)))).
 { apply(source_set_relativization_preserves_bound M matrix(code_numeral M 2)
     (succM M(succM M(succM M m))) relative);try assumption.
   do 2 apply coding_lt_succ_cancel. apply coding_zero_lt_succ. }
 assert(BL:source_bounded M(domain)(succM M(succM M m))).
 { apply(source_bounded_monotone M _ (code_numeral M 1) _ HD).
   apply coding_lt_succ_cancel,coding_zero_lt_succ. }
 assert(B: schema_expression_bound M(L_definable_profile_environment relative(domain))
  (E_L_definable_profile(CEvar 0)(CEvar 1))(succM M m)).
 { unfold E_L_definable_profile,E_sf_iff.
   repeat schema_constructor_bound;try schema_small_index.
   - exact BL.
   - exact BR. }
 exact(B result HO).
Qed.
Print Assumptions source_definable_profile_formula_correct.
Print Assumptions source_definable_profile_total.
Print Assumptions source_definable_profile_functional.
Print Assumptions source_definable_profile_bounded.


Definition source_L_definable_profile M phi result :=source_definable_profile M(source_L_domain_code M) phi result.
Theorem source_L_definable_profile_total M phi :exists result,source_L_definable_profile M phi result.
Proof. apply source_definable_profile_total. Qed.
Theorem source_L_definable_profile_bounded M m phi result :source_bounded M phi(succM M m) ->
 source_L_definable_profile M phi result ->source_bounded M result(succM M m).
Proof. apply(source_definable_profile_bounded M(source_L_domain_code M) m phi result(numerical_L_domain_bounded M)). Qed.
