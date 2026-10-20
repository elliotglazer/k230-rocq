(** Finite named compilation commutes with genuine source relativization.
 This is an actual map construction, with no proof or image assumption. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes FixedSourceBounds SourceNumeralLift
 SourceFiniteParameters SourceFiniteNameParameters NumericalRenamingMaps NumericalSubstitutionMaps RenamingSubstitution
 SourceRelativizationCalibration SourceRelativizationSubstitution.
From Undecidability.FOL Require Import Syntax.Bounded.
From Stdlib Require Import Arith.PeanoNat Lia.
Unset Implicit Arguments.
Theorem source_finite_parameter_name_map M count rho:exists b c,forall i x,
 code_relation M rho(source_finite_parameter_names count i)x->
 renaming_lookup M b c(code_numeral M count)(zeroM M)(code_numeral M i)x.
Proof.
 destruct(source_finite_names_total M count rho(zeroM M))as(b&c&HB).
 exists b,c. intros i x HX. unfold source_finite_parameter_names in HX.
 destruct(Nat.ltb_spec i count)as[HI|HI].
 - change(x=rho i)in HX. subst x. exact(HB i HI).
 - change(x=code_numeral M i)in HX. subst x.
   assert(HOutside:~coding_lt M(code_numeral M i)(code_numeral M count)).
   { intro H. apply(proj1(fixed_source_numeral_lt_iff M i count))in H. lia. }
   apply(proj2(renaming_lookup_outside M b c(code_numeral M count)(zeroM M)
    (code_numeral M i)(code_numeral M i)HOutside)). symmetry. apply coding_add_zero_r.
Qed.
Theorem source_finite_named_relativization M domain phi count rho raw relative:
 bounded 1 domain->
 code_relation M rho(source_parameter_expression(source_finite_parameter_names count)phi)raw->
 code_relation M rho(source_parameter_expression(source_finite_parameter_names count)(sf_relativize domain phi))relative->
 SourceRelativization.source_relativization M(code_numeral M(sf_encode domain))raw relative.
Proof.
 intros HD HRaw HRelative. destruct(source_finite_parameter_name_map M count rho)as(b&c&HMap).
 pose proof(source_finite_parameter_renaming M phi(source_finite_parameter_names count)rho b c
  (code_numeral M count)(zeroM M)raw HMap HRaw)as RRaw.
 pose proof(source_finite_parameter_renaming M(sf_relativize domain phi)(source_finite_parameter_names count)rho b c
  (code_numeral M count)(zeroM M)relative HMap HRelative)as RRelative.
 exact(source_relativization_substitution M(code_numeral M(sf_encode domain))
  (code_numeral M(sf_encode phi)) (code_numeral M(sf_encode(sf_relativize domain phi)))b c
  (code_numeral M count)(addM M(code_numeral M count)(zeroM M))raw relative
  (proj2(source_formula_numeral_bounded M domain 1)HD)
  (source_relativization_finite_lift M domain phi)
  (proj1(numerical_renaming_substitution M _ b c(code_numeral M count)(zeroM M)raw)RRaw)
  (proj1(numerical_renaming_substitution M _ b c(code_numeral M count)(zeroM M)relative)RRelative)).
Qed.
Print Assumptions source_finite_parameter_name_map.
Print Assumptions source_finite_named_relativization.
