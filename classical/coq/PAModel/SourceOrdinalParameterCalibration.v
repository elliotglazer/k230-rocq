(** Calibrate each Ord0 occurrence in the fixed original finite laws to
    the unary numerical Ord predicate used by the varying matrix recipes. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  OldNamedSyntaxBridge OldFullNDSourceBridge SourceOrdinalPredicate
  SourceFiniteParameters SourceFiniteParameterComposition SourceUnaryParameters
  NumericalInstantiation.
From OldZFC Require Z_base.
Unset Implicit Arguments.

Lemma isolated_ordinal_at t :
  isolated_formula (OldZFC.Z_base.Ord0 t) =
  C.subst_form (C.scons (isolated_term t) C.var) source_ordinal_predicate.
Proof.
  pose proof (isolated_old_formula_instantiate
    (OldZFC.Z_base.Ord0 (@OC.var OB.sig_empty 0)) t) as HE.
  rewrite OldZFC.Z_base.Ord0_subst in HE. exact HE.
Qed.

Theorem source_parameter_ordinal_instance M names rho i name out :
  code_relation M rho (names i) name ->
  code_relation M rho (source_parameter_expression names
    (isolated_formula (OldZFC.Z_base.Ord0 (@OC.var OB.sig_empty i)))) out ->
  numerical_instantiation M (source_ordinal_predicate_code M) name out.
Proof.
  intros HName HGraph. rewrite isolated_ordinal_at,source_parameter_substitution in HGraph.
  exact (source_unary_parameter_instantiation M source_ordinal_predicate
    (fun j=>names (sf_index ((C.scons (isolated_term (@OC.var OB.sig_empty i)) C.var) j)))
    rho name out source_ordinal_predicate_finite_bound HName HGraph).
Qed.

Print Assumptions isolated_ordinal_at.
Print Assumptions source_parameter_ordinal_instance.
