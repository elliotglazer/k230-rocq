(** Free-name bounds for the fixed recursion induction hypotheses. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SourceBounded SourceRecursionInductionGraphs
 SourceRecursionPrimitiveRelations SourceFiniteParameters SourceFiniteNameParameters SourceParameterGraphs SourceParameterTransport.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Theorem source_rec_totality_bounded M N out k:coding_lt M N k ->source_rec_totality M N out ->source_bounded M out k.
Proof.
 intros BN HO. apply(source_parameter_graph_bounded M 1 source_rec_totality_predicate source_rec_totality_finite_bound
  (source_finite_parameter_names 1)(fun _=>N)k);[|exact HO].
 intros[|i]x HI HX;[|lia]. change(x=N)in HX. now subst x.
Qed.
Theorem source_rec_induction_bounded M o N out k:coding_lt M o k ->coding_lt M N k ->source_rec_induction M o N out ->source_bounded M out k.
Proof.
 intros BO BN HO. apply(source_parameter_graph_bounded M 2 source_rec_induction_predicate source_rec_induction_finite_bound
  (source_finite_parameter_names 2)(source_rec_env2 o N)k);[|exact HO].
 intros[|[|i]]x HI HX;try lia.
 - change(x=o)in HX. now subst x.
 - change(x=N)in HX. now subst x.
Qed.
Print Assumptions source_rec_totality_bounded.
Print Assumptions source_rec_induction_bounded.
