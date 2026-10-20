(** The exact Ord0 predicate used by the pinned ordinal-collection recipe,
    with arbitrary-name instance graphs identified with ordinary source
    instantiation. The extensional equality is syntactic, not semantic. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceBounded SourceNumeralLift OldNamedSyntaxBridge OldFullNDSourceBridge
  SourceFiniteParameters SourceFiniteParameterProofs SourceFiniteParameterBounds
  NumericalInstantiation.
From OldZFC Require Z_base Z_refl Z_rel.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Definition source_ordinal_predicate : sf_form :=
  isolated_formula (OldZFC.Z_base.Ord0 (@OC.var OB.sig_empty 0)).
Definition source_ordinal_predicate_code M := code_numeral M (sf_encode source_ordinal_predicate).
Definition source_ordinal_instance M name out :=
  code_relation M (fun _=>name)
    (source_parameter_expression source_three_parameter_names source_ordinal_predicate) out.

Lemma source_ordinal_predicate_finite_bound :
  Undecidability.FOL.Syntax.Bounded.bounded 1 source_ordinal_predicate.
Proof.
  apply (@isolated_bounded OC.falsity_on 1 (OldZFC.Z_base.Ord0 (@OC.var OB.sig_empty 0))).
  exact (OldZFC.Z_rel.fb_bounded _ 1
    (OldZFC.Z_refl.fb_Ord0 (@OC.var OB.sig_empty 0) 1 ltac:(cbn;lia))).
Qed.

Theorem source_ordinal_predicate_bounded M :
  source_bounded M (source_ordinal_predicate_code M) (code_numeral M 1).
Proof.
  exact (proj2 (source_formula_numeral_bounded M source_ordinal_predicate 1)
    source_ordinal_predicate_finite_bound).
Qed.

Theorem source_ordinal_instance_total M name :exists out,source_ordinal_instance M name out.
Proof. apply code_relation_total. Qed.

Theorem source_ordinal_instance_exact M name out :
  source_ordinal_instance M name out <->
  numerical_instantiation M (source_ordinal_predicate_code M) name out.
Proof.
  split.
  - intro HG. exact (source_one_parameter_instantiation M source_ordinal_predicate
      (fun _=>name) out source_ordinal_predicate_finite_bound HG).
  - intro HInst. destruct (source_ordinal_instance_total M name) as [other HO].
    pose proof (source_one_parameter_instantiation M source_ordinal_predicate
      (fun _=>name) other source_ordinal_predicate_finite_bound HO) as HOther.
    pose proof (numerical_instantiation_functional M (source_ordinal_predicate_code M)
      name out other HInst HOther) as E. now subst out.
Qed.

Print Assumptions source_ordinal_predicate_finite_bound.
Print Assumptions source_ordinal_predicate_bounded.
Print Assumptions source_ordinal_instance_total.
Print Assumptions source_ordinal_instance_exact.

