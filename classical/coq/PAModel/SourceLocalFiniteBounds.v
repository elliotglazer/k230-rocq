(** Convenience wrappers for the exact finite parameter compiler. Only
    the genuinely used finite slots enter its bound and vacuity premises. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 SourceFiniteParameters SourceFiniteNameParameters SourceParameterGraphs SourceParameterVacuity SourceNamedVacuity.
From Undecidability.FOL Require Import Syntax.Bounded.
From Stdlib Require Import Arith.PeanoNat.
Unset Implicit Arguments.
Theorem source_local_finite_parameter_bound M arity(phi:sf_form)(HB:bounded arity phi)rho k out:
 (forall i,(i<arity)%nat ->coding_lt M(rho i)k) ->
 code_relation M rho(source_parameter_expression(source_finite_parameter_names arity)phi)out ->source_bounded M out k.
Proof.
 intros HI HG. apply(source_parameter_graph_bounded M arity phi HB(source_finite_parameter_names arity)rho k);[|exact HG].
 intros i v HIX HX. unfold source_finite_parameter_names in HX.
 assert(E:Nat.ltb i arity=true)by(exact(proj2(Nat.ltb_lt i arity)HIX)). rewrite E in HX.
 change(v=rho i)in HX. subst v. exact(HI i HIX).
Qed.
Theorem source_local_finite_parameter_vacuous M arity(phi:sf_form)(HB:bounded arity phi)rho x out:
 (forall i,(i<arity)%nat ->rho i<>x) ->
 code_relation M rho(source_parameter_expression(source_finite_parameter_names arity)phi)out ->source_named_vacuous M x out.
Proof.
 intros HI HG. apply(source_parameter_graph_named_vacuous M arity phi HB(source_finite_parameter_names arity)rho x);[|exact HG].
 intros i v HIX HX. unfold source_finite_parameter_names in HX.
 assert(E:Nat.ltb i arity=true)by(exact(proj2(Nat.ltb_lt i arity)HIX)). rewrite E in HX.
 change(v=rho i)in HX. subst v. exact(HI i HIX).
Qed.
Print Assumptions source_local_finite_parameter_bound.
Print Assumptions source_local_finite_parameter_vacuous.
