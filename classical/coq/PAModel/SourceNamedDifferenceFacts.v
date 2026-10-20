(** Exact finite syntax and name-vacuity facts for the conjunction frame.
    Arbitrary representation matrices do not occur in these calibrations. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 SourceNumeralLift SourceFiniteParameters SourceParameterGraphs SourceFiniteParameterProofs
 SourceNamedFiniteCalibration SourceNamedDifferenceCertificates SourceDifferenceProfile
 SourceNamedVacuity SourceRenamingDiamond SourceQuantifierRules NumericalContextRenaming
 NumericalRenamingMaps NumericalRenaming RawBinderRenaming FixedSourceBounds OldNamedSyntaxBridge OldFullNDSourceBridge.
From OldZFC Require Z_rel.
From Undecidability.FOL Require Import Syntax.Facts Syntax.Bounded Sets.minZF.
From Stdlib Require Import Arith.PeanoNat Lia.
Open Scope minZFsyn.
Unset Implicit Arguments.

Lemma source_finite_closing_graph M x(phi:sf_form)b c :
 raw_binder_renaming M(code_numeral M x)b c ->
 numerical_renaming M(code_numeral M(sf_encode phi))b c(succM M(code_numeral M x))(code_numeral M 1)
   (code_numeral M(sf_encode(source_finite_closing x phi))).
Proof.
 intro HM. apply(source_finite_parameter_renaming M phi
  (fun i=>CEconst(sf_index(source_finite_closing_substitution x i)))(fun _=>zeroM M)
  b c(succM M(code_numeral M x))(code_numeral M 1)_).
 - intros i v HV. change(v=code_numeral M(sf_index(source_finite_closing_substitution x i)))in HV. subst v.
   unfold source_finite_closing_substitution. destruct(Nat.eq_dec i x)as[->|HIX].
   + apply(proj2(HM(code_numeral M x)(zeroM M))). now left.
   + apply(proj2(HM(code_numeral M i)(code_numeral M(S i)))). right.
     exact(conj(source_fixed_numeral_neq M i x HIX)eq_refl).
 - exact(source_parameter_substitution_calibration M phi(source_finite_closing_substitution x)).
Qed.

Theorem source_finite_named_vacuity M x(phi:sf_form) :
 source_finite_closing x phi=phi[↑] ->source_named_vacuous M(code_numeral M x)(code_numeral M(sf_encode phi)).
Proof.
 intros HE b c g shifted HM HG HS.
 rewrite(numerical_renaming_functional M _ b c _ _ g _ HG(source_finite_closing_graph M x phi b c HM)).
 rewrite HE.
 apply(numerical_renaming_functional M(code_numeral M(sf_encode phi))
  (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)
  (code_numeral M(sf_encode(phi[↑]))) shifted);[|exact HS].
 apply(source_finite_parameter_renaming M phi(fun i=>CEconst(S i))(fun _=>zeroM M)
  (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)_).
 - intros i v HV. change(v=code_numeral M(S i))in HV. subst v.
   apply(proj2(context_shift_lookup M(code_numeral M i)(code_numeral M(S i)))). reflexivity.
 - exact(source_parameter_substitution_calibration M phi(fun i=>$ (S i))).
Qed.

Theorem named_difference_conditions_vacuous M x :
 (x=0\/x=3\/x=4\/x=5) ->
 source_named_vacuous M(code_numeral M x)(code_numeral M(sf_encode named_difference_successor)) /\
 source_named_vacuous M(code_numeral M x)(code_numeral M(sf_encode named_difference_closure)).
Proof.
 intros [H | [H | [H | H]]];subst x;split;apply source_finite_named_vacuity;reflexivity.
Qed.

Theorem named_difference_member_vacuous M x r :x<>r ->x<>2 ->
 source_named_vacuous M(code_numeral M x)(code_numeral M(sf_encode($(r) ∈' $2))).
Proof.
 intros HXR HX2. apply source_finite_named_vacuity.
 change(((source_finite_closing_substitution x r) ∈'(source_finite_closing_substitution x 2))=
   ($(S r) ∈' $3)).
 unfold source_finite_closing_substitution.
 destruct(Nat.eq_dec r x), (Nat.eq_dec 2 x);try congruence. reflexivity.
Qed.

Theorem named_difference_fixed_bounds M :
 source_bounded M(code_numeral M(sf_encode named_difference_successor))(code_numeral M 8) /\
 source_bounded M(code_numeral M(sf_encode named_difference_closure))(code_numeral M 8).
Proof.
 split;apply(proj2(source_formula_numeral_bounded M _ 8));
 unfold named_difference_successor,named_difference_closure;
 apply(@isolated_bounded OC.falsity_on 8),OldZFC.Z_rel.fb_bounded,OldZFC.Z_rel.fbb_fb;reflexivity.
Qed.

Print Assumptions source_finite_named_vacuity.
Print Assumptions named_difference_conditions_vacuous.
Print Assumptions named_difference_member_vacuous.
Print Assumptions named_difference_fixed_bounds.
