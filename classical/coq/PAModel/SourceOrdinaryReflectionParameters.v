(** The fixed ordinary Refl formula compiled at arbitrary model-valued
 ordinal names is exactly the uniform arithmetic reflection graph. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes StandardModel SourceNumeralLift
 OldNamedSyntaxBridge SourceFiniteParameters SourceLFixed SourceOrdinaryReflectionCalibration SourceOrdinaryReflectionSyntax SourceOrdinaryReflectionTransport
 SourceBoundedCalibration SourceUnaryParameters NumericalSubstitution NumericalInstantiation.
From Undecidability.FOL Require Import Syntax.Bounded.
Unset Implicit Arguments.
Local Opaque source_L_domain source_L_domain_code.
Theorem source_ordinary_reflection_finite_bound n(phi:isolated_old_form OC.falsity_on):
 bounded n(isolated_formula phi)->bounded 1(isolated_formula(OldZFC.Z_refl.Refl n phi(@OC.var OB.sig_empty 0))).
Proof.
 intro HP. apply(proj1(source_formula_numeral_bounded natModel _ 1)).
 exact(source_ordinary_reflection_bounded natModel(source_L_domain_code natModel)(code_numeral natModel n)
  (code_numeral natModel(sf_encode(isolated_formula phi)))(code_numeral natModel 0)
  (code_numeral natModel(sf_encode(isolated_formula(OldZFC.Z_refl.Refl n phi(@OC.var OB.sig_empty 0)))))
  (code_numeral natModel 1)(numerical_L_domain_bounded natModel)
  (proj2(source_formula_numeral_bounded natModel(isolated_formula phi)n)HP)
  (coding_zero_lt_succ natModel(zeroM natModel))(source_ordinary_reflection_finite_lift natModel n phi 0)).
Qed.
Theorem source_parameter_ordinary_reflection M n(phi:isolated_old_form OC.falsity_on)names rho d out:
 bounded n(isolated_formula phi)->code_relation M rho(names 0)d->
 code_relation M rho(source_parameter_expression names
  (isolated_formula(OldZFC.Z_refl.Refl n phi(@OC.var OB.sig_empty 0))))out->
 source_ordinary_reflection M(source_L_domain_code M)(code_numeral M n)
  (code_numeral M(sf_encode(isolated_formula phi)))d out.
Proof.
 intros HP HName HO.
 destruct(source_unary_parameter_instantiation M _ names rho d out
  (source_ordinary_reflection_finite_bound n phi HP)HName HO)as(b&c&HHead&HSub).
 destruct(source_ordinary_reflection_total M(source_L_domain_code M)(code_numeral M n)
  (code_numeral M(sf_encode(isolated_formula phi)))d)as(out'&HOut').
 pose proof(source_ordinary_reflection_substitution M(source_L_domain_code M)(code_numeral M n)
  (code_numeral M(sf_encode(isolated_formula phi)))(zeroM M)
  (code_numeral M(sf_encode(isolated_formula(OldZFC.Z_refl.Refl n phi(@OC.var OB.sig_empty 0)))))d out'
  b c(succM M(zeroM M))(zeroM M)(numerical_L_domain_bounded M)
  (proj2(source_formula_numeral_bounded M(isolated_formula phi)n)HP)
  (source_ordinary_reflection_finite_lift M n phi 0)HOut' HHead)as HSub'.
 pose proof(numerical_substitution_functional M _ b c(succM M(zeroM M))(zeroM M)out out' HSub HSub')as E.
 now subst out'.
Qed.
Print Assumptions source_ordinary_reflection_finite_bound.
Print Assumptions source_parameter_ordinary_reflection.
