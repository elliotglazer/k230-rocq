(** Literal Ext0 survives the two cutoff2 insertions followed by the
 twice-lifted Dn rotation. This finite calibration is independent of EnvF. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceNumeralLift
 SourceDefinabilityPrimitives SourceFiniteCutoffShift SourceQfFunctionality SourceFiniteParameters
 SourceNamedFiniteCalibration SourceEnvironmentStepMaps NumericalRenamingMaps NumericalRenaming.
From FOL Require Import FullSyntax.
From Undecidability.FOL Require Import Syntax.Core Syntax.BinSig Sets.Signatures.
Unset Implicit Arguments.
Definition environment_shifted_extension:sf_form:=
 subst_form(source_shift_sigma 2)(subst_form(source_shift_sigma 2)source_def_extension021).
Definition environment_rotation_sigma i:sf_term:=var(match i with 0=>0|1=>1|2=>3|3=>4|4=>2|_=>i end).
Lemma environment_extension_rotation_literal:
 subst_form environment_rotation_sigma environment_shifted_extension=source_def_extension021.
Proof. reflexivity. Qed.
Theorem source_environment_extension_twice_cutoff M first second:
 source_cutoff_shift M 2(code_numeral M(sf_encode source_def_extension021))first ->
 source_cutoff_shift M 2 first second ->second=code_numeral M(sf_encode environment_shifted_extension).
Proof.
 intros H1 H2.
 pose proof(source_cutoff_shift_fixed_source M 2(fun _=>zeroM M)source_def_extension021 _ _
  (source_formula_numeral_graph M source_def_extension021)
  (source_formula_numeral_graph M(subst_form(source_shift_sigma 2)source_def_extension021)))as HC1.
 rewrite(source_cutoff_shift_functional M 2 _ first _ H1 HC1)in H2.
 pose proof(source_cutoff_shift_fixed_source M 2(fun _=>zeroM M)(subst_form(source_shift_sigma 2)source_def_extension021) _ _
  (source_formula_numeral_graph M(subst_form(source_shift_sigma 2)source_def_extension021))
  (source_formula_numeral_graph M environment_shifted_extension))as HC2.
 exact(source_cutoff_shift_functional M 2 _ second _ H2 HC2).
Qed.
Theorem source_environment_extension_rotation M first second b c n d e l:
 source_cutoff_shift M 2(code_numeral M(sf_encode source_def_extension021))first ->
 source_cutoff_shift M 2 first second ->environment_rotation_lifts M b c n d e l ->
 numerical_renaming M second d e l(zeroM M)(code_numeral M(sf_encode source_def_extension021)).
Proof.
 intros H1 H2 HL. rewrite(source_environment_extension_twice_cutoff M first second H1 H2).
 rewrite<-environment_extension_rotation_literal.
 apply(source_finite_parameter_renaming M environment_shifted_extension
  (fun i=>CEconst(sf_index(environment_rotation_sigma i)))(fun _=>zeroM M)d e l(zeroM M)).
 - intros[|[|[|[|[|i]]]]]v HV;cbn[code_relation environment_rotation_sigma sf_index]in HV;subst v.
   + exact(environment_rotation_zero M b c n d e l HL).
   + exact(environment_rotation_one M b c n d e l HL).
   + exact(environment_rotation_two M b c n d e l HL).
   + exact(environment_rotation_three M b c n d e l HL).
   + exact(environment_rotation_four M b c n d e l HL).
   + exact(environment_rotation_above M b c n d e l(code_numeral M i)HL).
 - exact(source_parameter_substitution_calibration M environment_shifted_extension environment_rotation_sigma).
Qed.
Print Assumptions source_environment_extension_twice_cutoff.
Print Assumptions source_environment_extension_rotation.
