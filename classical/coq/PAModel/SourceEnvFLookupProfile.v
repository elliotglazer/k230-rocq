(** Exact application lookup profiles at arbitrary model-valued names. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs SetFormulaCodes SourceBounded
 OldNamedSyntaxBridge OldFullNDSourceBridge SourceAtomLookupOld SourceFiniteParameters SourceFiniteNameParameters
 SourceParameterGraphs SourceParameterTransport NumericalSubstitutionMaps NumericalSubstitution.
From OldZFC Require Z_rel.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
Definition source_env_profile_predicate:sf_form:=isolated_formula(old_atom_app_profile
 (@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2)).
Definition source_env_profile_expression:=source_parameter_expression(source_finite_parameter_names 3)source_env_profile_predicate.
Definition source_env_profile_environment{A:Type}(e i a:A)(idx:nat):=match idx with 0=>e|1=>i|_=>a end.
Definition source_env_profile M e i a out:=code_relation M(source_env_profile_environment e i a)source_env_profile_expression out.
Definition source_env_profile_formula(e i a out:term):form:=code_formula source_env_profile_expression(source_env_profile_environment e i a)out.
Local Opaque holds code_formula code_relation source_env_profile_expression.
Theorem source_env_profile_formula_correct M rho e i a out:holds M rho(source_env_profile_formula e i a out)<->
 source_env_profile M(evalM M rho e)(evalM M rho i)(evalM M rho a)(evalM M rho out).
Proof.
 unfold source_env_profile_formula,source_env_profile. rewrite code_formula_correct.
 apply code_relation_ext. intros[|[|idx]];reflexivity.
Qed.
Theorem source_env_profile_total M e i a:exists out,source_env_profile M e i a out.
Proof. apply code_relation_total. Qed.
Theorem source_env_profile_functional M e i a x y:source_env_profile M e i a x ->source_env_profile M e i a y ->x=y.
Proof. apply code_relation_functional. Qed.
Lemma source_env_profile_finite_bound:Undecidability.FOL.Syntax.Bounded.bounded 3 source_env_profile_predicate.
Proof.
 apply(@isolated_bounded OC.falsity_on 3(old_atom_app_profile(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2))).
 apply OldZFC.Z_rel.fb_bounded,OldZFC.Z_rel.fbb_fb. reflexivity.
Qed.
Theorem source_env_profile_bounded M e i a out k:coding_lt M e k ->coding_lt M i k ->coding_lt M a k ->
 source_env_profile M e i a out ->source_bounded M out k.
Proof.
 intros HE HI HA HO. apply(source_parameter_graph_bounded M 3 source_env_profile_predicate source_env_profile_finite_bound
  (source_finite_parameter_names 3)(source_env_profile_environment e i a)k);[|exact HO].
 intros[|[|[|idx]]] x HX HName;try lia.
 - change(x=e)in HName. now subst x.
 - change(x=i)in HName. now subst x.
 - change(x=a)in HName. now subst x.
Qed.
Theorem source_env_profile_substitution M e i a old e' i' a' new b c n base:
 source_env_profile M e i a old ->source_env_profile M e' i' a' new ->
 substitution_lookup M b c n base e e' ->substitution_lookup M b c n base i i' ->substitution_lookup M b c n base a a' ->
 numerical_substitution M old b c n base new.
Proof.
 intros HO HN HE HI HA. apply(source_parameter_transport M 3 source_env_profile_predicate source_env_profile_finite_bound
  (source_finite_parameter_names 3)(source_finite_parameter_names 3)
  (source_env_profile_environment e i a)(source_env_profile_environment e' i' a')b c n base old new);[|exact HO|exact HN].
 intros[|[|[|idx]]] x y HX HO' HN';try lia.
 - change(x=e)in HO'. change(y=e')in HN'. now subst x y.
 - change(x=i)in HO'. change(y=i')in HN'. now subst x y.
 - change(x=a)in HO'. change(y=a')in HN'. now subst x y.
Qed.
Print Assumptions source_env_profile_formula_correct.
Print Assumptions source_env_profile_total.
Print Assumptions source_env_profile_functional.
Print Assumptions source_env_profile_finite_bound.
Print Assumptions source_env_profile_bounded.
Print Assumptions source_env_profile_substitution.
