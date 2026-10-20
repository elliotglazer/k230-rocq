(** Finite named-binder calibration used only for fixed operation
    certificates. Arbitrary internal representation matrices use the
    separate arithmetic renaming and vacuity theorems. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
 SourceFiniteParameters SourceFiniteParameterComposition SourceParameterIdentityCalibration SourceNumeralLift
 NumericalRenamingMaps NumericalRenaming RawBinderRenaming SourceNamedQuantifierRules.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From Stdlib Require Import Arith.PeanoNat Lia.
Open Scope minZFsyn.
Unset Implicit Arguments.
Definition source_finite_closing_substitution x i :sf_term :=if Nat.eq_dec i x then $0 else $(S i).
Definition source_finite_closing x(phi:sf_form):sf_form :=phi[source_finite_closing_substitution x].
Lemma source_fixed_numeral_neq M i j :i<>j ->code_numeral M i<>code_numeral M j.
Proof.
 revert j. induction i as[|i IH];intros[|j] HI E;try contradiction.
 - exact(Model.zero_ne_succ M(code_numeral M j) E).
 - exact(Model.zero_ne_succ M(code_numeral M i)(eq_sym E)).
 - apply(Model.succ_injective M)in E. apply(IH j);[lia|exact E].
Qed.
Lemma source_parameter_substitution_calibration M(phi:sf_form)sigma :
 code_relation M(fun _=>zeroM M)
  (source_parameter_expression(fun i=>CEconst(sf_index(sigma i)))phi)
  (code_numeral M(sf_encode(phi[sigma]))).
Proof.
 rewrite <-(source_parameter_substitution phi(fun i=>CEconst i)sigma).
 apply source_parameter_identity_calibration. intro i. reflexivity.
Qed.
Theorem source_finite_named_quantifier_calibration M universal x(phi:sf_form) :
 source_named_quantifier M universal(code_numeral M x)(code_numeral M(sf_encode phi))
  (code_numeral M(sf_encode(if universal then ∀(source_finite_closing x phi) else ∃(source_finite_closing x phi)))).
Proof.
 destruct(raw_binder_renaming_total M(code_numeral M x))as(b&c&HM).
 exists b,c,(code_numeral M(sf_encode(source_finite_closing x phi))). split;[exact HM|]. split.
 - apply(source_finite_parameter_renaming M phi
    (fun i=>CEconst(sf_index(source_finite_closing_substitution x i)))(fun _=>zeroM M)
    b c(succM M(code_numeral M x))(code_numeral M 1)(code_numeral M(sf_encode(source_finite_closing x phi)))).
   + intros i v HV. change(v=code_numeral M(sf_index(source_finite_closing_substitution x i)))in HV. subst v.
     unfold source_finite_closing_substitution. destruct(Nat.eq_dec i x)as[->|HIX].
     * apply(proj2(HM(code_numeral M x)(zeroM M))). left. auto.
     * apply(proj2(HM(code_numeral M i)(code_numeral M(S i)))). right.
       exact(conj(source_fixed_numeral_neq M i x HIX)eq_refl).
   + exact(source_parameter_substitution_calibration M phi(source_finite_closing_substitution x)).
 - destruct universal;cbn[sf_encode].
   + exact(sf_make_numeral M SFAll(sf_encode(source_finite_closing x phi))0).
   + exact(sf_make_numeral M SFEx(sf_encode(source_finite_closing x phi))0).
Qed.
Print Assumptions source_finite_named_quantifier_calibration.

