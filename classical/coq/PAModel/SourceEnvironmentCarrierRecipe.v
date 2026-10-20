(** The literal carrier invariant for An: under every A-valued assignment,
    every EnvF environment belongs to representative0. This graph contains
    only syntax and arbitrary-count Dn; existence of an An in C is separate. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes SourceBounded NumericalProofs
 SourceDefinabilityIteration SourceDefinabilityBounds SourceFiniteCutoffShift SourceQfFunctionality SourceDn SourceDnBounds
 SchemaConstructorBounds SourceRepresentationRecipe.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature |0.
#[local] Existing Instance PA_preds_signature |0.

Definition E_environment_carrier_point:=E_sf SFAll
 (E_sf SFImpl(CEvar 0)(E_sf SFMember(CEconst 0)(CEconst 1)))(CEconst 0).
Definition source_environment_carrier_recipe M count result:=exists environment first guard point,
 source_envf M count environment /\source_cutoff_shift M 1 environment first /\
 source_cutoff_shift M 1 first guard /\code_relation M(fun _=>guard)E_environment_carrier_point point /\
 source_dn M count point result.
Definition carrier_lift4(t:term):term:=t`[↑]`[↑]`[↑]`[↑].
Definition source_environment_carrier_recipe_formula(count result:term):form:=∃∃∃∃(
 source_envf_formula(carrier_lift4 count)$3 ∧
 (source_cutoff_shift_formula 1 $3 $2 ∧
 (source_cutoff_shift_formula 1 $2 $1 ∧
 (code_formula E_environment_carrier_point(fun _=>$1)$0 ∧
 source_dn_formula(carrier_lift4 count)$0(carrier_lift4 result))))).
Lemma carrier_eval_lift4 M rho a b c d t:evalM M(d .:c .:b .:a .:rho)(carrier_lift4 t)=evalM M rho t.
Proof. unfold evalM,carrier_lift4. now rewrite !eval_up. Qed.
Local Opaque holds source_envf_formula source_cutoff_shift_formula code_formula source_dn_formula code_relation.
Theorem source_environment_carrier_recipe_formula_correct M rho count result:
 holds M rho(source_environment_carrier_recipe_formula count result)<->
 source_environment_carrier_recipe M(evalM M rho count)(evalM M rho result).
Proof.
 unfold source_environment_carrier_recipe_formula,source_environment_carrier_recipe.
 repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
 setoid_rewrite source_envf_formula_correct. setoid_rewrite source_cutoff_shift_formula_correct.
 setoid_rewrite code_formula_correct. setoid_rewrite source_dn_formula_correct.
 setoid_rewrite carrier_eval_lift4.
 split;intros(environment&first&guard&point&HE&H1&H2&HP&HD);exists environment,first,guard,point;
  refine(conj HE(conj H1(conj H2(conj _ HD))));exact HP.
Qed.
Theorem source_environment_carrier_recipe_total M count:exists result,source_environment_carrier_recipe M count result.
Proof.
 destruct(source_envf_total M count)as(environment&HE).
 destruct(source_cutoff_shift_total M 1 environment)as(first&H1).
 destruct(source_cutoff_shift_total M 1 first)as(guard&H2).
 destruct(code_relation_total M E_environment_carrier_point(fun _=>guard))as(point&HP).
 destruct(source_dn_total M count point)as(result&HD).
 exists result,environment,first,guard,point. exact(conj HE(conj H1(conj H2(conj HP HD)))).
Qed.
Theorem source_environment_carrier_recipe_functional M count result other:
 source_environment_carrier_recipe M count result ->source_environment_carrier_recipe M count other ->result=other.
Proof.
 intros(e&f&g&p&HE&H1&H2&HP&HD)(e'&f'&g'&p'&HE'&H1'&H2'&HP'&HD').
 assert(e=e')by(eapply source_def_iteration_functional;eassumption). subst e'.
 assert(f=f')by(eapply source_cutoff_shift_functional;eassumption). subst f'.
 assert(g=g')by(eapply source_cutoff_shift_functional;eassumption). subst g'.
 assert(p=p')by(eapply code_relation_functional;eassumption). subst p'.
 eapply source_dn_functional;eassumption.
Qed.
Theorem source_environment_carrier_recipe_bounded M count result:
 source_environment_carrier_recipe M count result ->source_bounded M result(code_numeral M 2).
Proof.
 intros(e&f&g&p&HE&H1&H2&HP&HD).
 pose proof(source_cutoff_shift_bounded M 1 e f count(source_envf_bound M count e HE)H1)as BF.
 pose proof(source_cutoff_shift_bounded M 1 f g(succM M count)BF H2)as BG.
 assert(BP:source_bounded M p(succM M(succM M count))).
 { assert(B:schema_expression_bound M(fun _=>g)E_environment_carrier_point(succM M(succM M count))).
   { unfold E_environment_carrier_point. repeat schema_constructor_bound;try schema_small_index;exact BG. }
   exact(B p HP). }
 apply(source_dn_bounded M count p result(zeroM M)HD).
 change(source_bounded M p(addM M count(code_numeral M 2))).
 rewrite Arithmetic.add_comm. change(source_bounded M p(addM M(succM M(succM M(zeroM M)))count)).
 now rewrite !Arithmetic.add_succ,Arithmetic.add_zero.
Qed.
Print Assumptions source_environment_carrier_recipe_formula_correct.
Print Assumptions source_environment_carrier_recipe_total.
Print Assumptions source_environment_carrier_recipe_functional.
Print Assumptions source_environment_carrier_recipe_bounded.
