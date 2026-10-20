(** Ordinary free-variable bounds for the finite lookup shells. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SetCodeDescent SourceBounded
 SourceDomainInstances SourceEnvFLookupProfile SourceEnvFLookupFiniteProofs SourceEnvFDomainWitnessBounds
 SourceImplicationAllShift SourceQuantifierRules NumericalInstantiation TaggedSelectedAllocation.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_profile_has_bound M e i a f:source_env_profile M e i a f->source_has_bound M f.
Proof.
 intro HF. exists(finite_name_bound M[e;i;a]). apply(source_env_profile_bounded M e i a f(finite_name_bound M[e;i;a]));
 [apply finite_name_bound_above;now left|apply finite_name_bound_above;right;now left|
 apply finite_name_bound_above;right;right;now left|exact HF].
Qed.
Theorem source_unary_instance_has_bound M unary i f:source_bounded M unary(code_numeral M 1)->
 numerical_instantiation M unary i f->source_has_bound M f.
Proof. intros HB HF. exists(succM M i). exact(source_domain_instance_bound M unary i f(succM M i)HB(coding_lt_succ M i)HF). Qed.
Theorem source_has_bound_binary_join M h a b f:sf_binary h->sf_relation M h a b f->
 source_has_bound M a->source_has_bound M b->source_has_bound M f.
Proof.
 intros HH HF HA HB. destruct(source_finite_common_bound M[a;b]ltac:(intros q[<-|[<-|[]]];assumption))as(k&HK).
 exists k. exact(ew_binary_bound M a b f k h HH HF(HK a(or_introl eq_refl))(HK b(or_intror(or_introl eq_refl)))).
Qed.
Theorem source_has_bound_ex_join M body ex:sf_relation M SFEx body(zeroM M)ex->source_has_bound M body->source_has_bound M ex.
Proof. intros HE(k&HB). exists k. exact(ew_exists_bound M body ex k HE HB). Qed.
Theorem source_has_bound_shift M f g:source_formula_shift M f g->source_has_bound M f->source_has_bound M g.
Proof. intros HS(k&HB). exists(succM M k). exact(source_shift_bound M f g k HB HS). Qed.
Print Assumptions source_profile_has_bound.
Print Assumptions source_unary_instance_has_bound.
Print Assumptions source_has_bound_binary_join.
