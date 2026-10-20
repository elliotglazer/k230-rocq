(** A first-order source statement of the representation invariant used
    in Z_cl.rep_ex. Dn binds arbitrarily many assignment variables while
    retaining the representative R at0 and its carrier A at1. No external
    assignment function or unproved source-proofs predicate occurs in the graph. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions NumericalProofs
 SetFormulaCodes SourceBounded SourceBoundMonotone SourceDefinabilityPrimitives SourceDefinabilityBounds
 SourceDefinabilityIteration SourceFiniteCutoffShift SourceQfFunctionality NumericalRenamingMaps NumericalRenaming
 SourceRenamingBounds SourceSetRelativization SourceSetRelativizationFunctionality SourceSetRelativizationBounds
 SourceDn SourceDnBounds SourceRelativizationRules SetSchemaConstructors SchemaConstructorBounds.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
Definition E_representation_point environment matrix :=E_sf SFAll
 (E_sf SFImpl environment(E_sf_iff(E_sf SFMember(CEconst 0)(CEconst 1)) matrix))(CEconst 0).
Definition representation_point_environment {A}(environment matrix:A) i :=match i with 0=>environment|_=>matrix end.
Definition source_representation_recipe M n phi result :=exists environment first shifted matrix relative body,
 source_envf M n environment /\source_cutoff_shift M 1 environment first /\
 source_cutoff_shift M 1 first shifted /\
 numerical_renaming M phi(zeroM M)(zeroM M)(zeroM M)(code_numeral M 3) matrix /\
 source_set_relativization M(code_numeral M 2) matrix relative /\
 code_relation M(representation_point_environment shifted relative)(E_representation_point(CEvar 0)(CEvar 1)) body /\
 source_dn M n body result.
Definition rep_lift6(t:term):term :=t`[↑]`[↑]`[↑]`[↑]`[↑]`[↑].
Definition source_representation_recipe_formula(n phi result:term):form :=∃∃∃∃∃∃(
 source_envf_formula(rep_lift6 n) $5 ∧
 (source_cutoff_shift_formula 1 $5 $4 ∧
 (source_cutoff_shift_formula 1 $4 $3 ∧
 (numerical_renaming_formula(rep_lift6 phi) zero zero zero(num 3) $2 ∧
 (source_set_relativization_formula(num 2) $2 $1 ∧
 (code_formula(E_representation_point(CEvar 0)(CEvar 1))
   (representation_point_environment $3 $1) $0 ∧
 source_dn_formula(rep_lift6 n) $0(rep_lift6 result))))))).
Lemma rep_eval_lift6 M rho a b c d e f t :evalM M(f .: e .: d .: c .: b .: a .: rho)(rep_lift6 t)=evalM M rho t.
Proof. unfold evalM,rep_lift6. now rewrite !eval_up. Qed.
Local Opaque holds source_envf_formula source_cutoff_shift_formula numerical_renaming_formula
 source_set_relativization_formula code_formula source_dn_formula code_relation.
Theorem source_representation_recipe_formula_correct M rho n phi result :
 holds M rho(source_representation_recipe_formula n phi result)<->
 source_representation_recipe M(evalM M rho n)(evalM M rho phi)(evalM M rho result).
Proof.
 unfold source_representation_recipe_formula,source_representation_recipe.
 repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
 setoid_rewrite source_envf_formula_correct. setoid_rewrite source_cutoff_shift_formula_correct.
 setoid_rewrite numerical_renaming_formula_correct. setoid_rewrite source_set_relativization_formula_correct.
 setoid_rewrite code_formula_correct. setoid_rewrite source_dn_formula_correct.
 setoid_rewrite rep_eval_lift6. repeat setoid_rewrite code_eval_num.
 split;intros(env&first&shifted&matrix&relative&body&HE&H1&H2&HM&HR&HB&HO);
  exists env,first,shifted,matrix,relative,body;
  refine(conj HE(conj H1(conj H2(conj HM(conj HR(conj _ HO)))))).
 - apply(proj1(code_relation_ext M(E_representation_point(CEvar 0)(CEvar 1))
    (fun index=>evalM M(body .: relative .: matrix .: shifted .: first .: env .: rho)
      (representation_point_environment $3 $1 index))
    (representation_point_environment shifted relative) body ltac:(intros[|i];reflexivity))). exact HB.
 - apply(proj2(code_relation_ext M(E_representation_point(CEvar 0)(CEvar 1))
    (fun index=>evalM M(body .: relative .: matrix .: shifted .: first .: env .: rho)
      (representation_point_environment $3 $1 index))
    (representation_point_environment shifted relative) body ltac:(intros[|i];reflexivity))). exact HB.
Qed.
Theorem source_representation_recipe_total M n phi :exists result,source_representation_recipe M n phi result.
Proof.
 destruct(source_envf_total M n)as(env&HE).
 destruct(source_cutoff_shift_total M 1 env)as(first&H1).
 destruct(source_cutoff_shift_total M 1 first)as(shifted&H2).
 destruct(numerical_renaming_total M phi(zeroM M)(zeroM M)(zeroM M)(code_numeral M 3))as(matrix&HM).
 destruct(source_set_relativization_total M(code_numeral M 2) matrix)as(relative&HR).
 destruct(code_relation_total M(E_representation_point(CEvar 0)(CEvar 1))
   (representation_point_environment shifted relative))as(body&HB).
 destruct(source_dn_total M n body)as(result&HO).
 exists result,env,first,shifted,matrix,relative,body. exact(conj HE(conj H1(conj H2(conj HM(conj HR(conj HB HO)))))).
Qed.
Theorem source_representation_recipe_functional M n phi result other :
 source_representation_recipe M n phi result ->source_representation_recipe M n phi other ->result=other.
Proof.
 intros(e&a&b&m&r&s&HE&H1&H2&HM&HR&HS&HO)(e'&a'&b'&m'&r'&s'&HE'&H1'&H2'&HM'&HR'&HS'&HP).
 assert(e=e')by(eapply source_def_iteration_functional;eassumption). subst e'.
 assert(a=a')by(eapply source_cutoff_shift_functional;eassumption). subst a'.
 assert(b=b')by(eapply source_cutoff_shift_functional;eassumption). subst b'.
 assert(m=m')by(eapply numerical_renaming_functional;eassumption). subst m'.
 assert(r=r')by(eapply source_set_relativization_functional;eassumption). subst r'.
 assert(s=s')by(eapply code_relation_functional;eassumption). subst s'.
 eapply source_dn_functional;eassumption.
Qed.
Theorem source_representation_recipe_bounded M n phi result :source_bounded M phi n ->
 source_representation_recipe M n phi result ->source_bounded M result(code_numeral M 2).
Proof.
 intros HP(e&a&b&m&r&s&HE&H1&H2&HM&HR&HS&HO).
 pose proof(source_cutoff_shift_bounded M 1 e a n(source_envf_bound M n e HE) H1)as BA.
 pose proof(source_cutoff_shift_bounded M 1 a b(succM M n) BA H2)as BB.
 assert(BM:source_bounded M m(succM M(succM M(succM M n)))).
 { apply(numerical_renaming_preserves_bound M phi _ _ _ _ m n _ HP HM).
   intros i j HI HJ. apply(renaming_lookup_outside M(zeroM M)(zeroM M)(zeroM M)
     (code_numeral M 3) i j(coding_not_lt_zero M i)) in HJ. subst j.
   rewrite Arithmetic.add_comm. change(coding_lt M(addM M(succM M(succM M(succM M(zeroM M)))) i)
     (succM M(succM M(succM M n)))).
   rewrite !Arithmetic.add_succ,Arithmetic.add_zero.
   do 3 apply coding_lt_succ_cancel. exact HI. }
 assert(BR:source_bounded M r(succM M(succM M(succM M n)))).
 { apply(source_set_relativization_preserves_bound M m(code_numeral M 2) _ r);try assumption.
   do 2 apply coding_lt_succ_cancel. apply coding_zero_lt_succ. }
 assert(BS:source_bounded M s(succM M(succM M n))).
 { assert(B: schema_expression_bound M(representation_point_environment b r)
     (E_representation_point(CEvar 0)(CEvar 1))(succM M(succM M n))).
   { unfold E_representation_point,E_sf_iff.
     repeat schema_constructor_bound;try schema_small_index;assumption. }
   exact(B s HS). }
 apply(source_dn_bounded M n s result(zeroM M) HO).
 change(source_bounded M s(addM M n(code_numeral M 2))).
 rewrite Arithmetic.add_comm. change(source_bounded M s(addM M(succM M(succM M(zeroM M))) n)).
 now rewrite !Arithmetic.add_succ,Arithmetic.add_zero.
Qed.
Print Assumptions source_representation_recipe_formula_correct.
Print Assumptions source_representation_recipe_total.
Print Assumptions source_representation_recipe_functional.
Print Assumptions source_representation_recipe_bounded.
