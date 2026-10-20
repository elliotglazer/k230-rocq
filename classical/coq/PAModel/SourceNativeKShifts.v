(** The literal up-shift in KPSeed.output_root keeps its container at 0. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  SetFormulaCodes SourceBounded SourceRenamingBounds NumericalRenamingMaps NumericalRenaming
  NumericalSubstitution RenamingSubstitution SchemaRenamingDescriptors NumericalEnvironments
  SourceNumeralLift SubstitutionSource.
From Undecidability.FOL Require Import Syntax.Core Syntax.Facts Syntax.BinSig Sets.Signatures.
From FOL Require Import FullSyntax.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Definition source_native_k_upshift M f g := numerical_renaming M f (zeroM M) (zeroM M)
  (code_numeral M 1) (code_numeral M 1) g.
Lemma source_native_k_upshift_zero M :
  renaming_lookup M (zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M 1)(zeroM M)(zeroM M).
Proof.
  apply (proj2(renaming_lookup_inside M _ _ _ _ _ _ (coding_zero_lt_succ M (zeroM M)))).
  apply (descriptor_beta_certificate M 0 0 0 0 0);reflexivity||lia.
Qed.
Lemma source_native_k_upshift_fixed_lookup M i :
  renaming_lookup M (zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M 1)
    (code_numeral M i)(code_numeral M(sf_index(up ↑ i))).
Proof.
  destruct i as [|i];[exact(source_native_k_upshift_zero M)|].
  apply renaming_lookup_outside.
  - intro H. change(coding_lt M (succM M(code_numeral M i))(succM M(zeroM M))) in H.
    apply (proj1(coding_lt_succ_cancel M _ _)) in H. exact(coding_not_lt_zero M _ H).
  - rewrite descriptor_numeral_add. f_equal. change(S(S i)=S i+1). lia.
Qed.
Theorem source_native_k_upshift_bound M f g k :
  source_bounded M f (succM M k) ->source_native_k_upshift M f g ->source_bounded M g (succM M(succM M k)).
Proof.
  intros HF HG. apply(numerical_renaming_preserves_bound M f _ _ _ _ g _ _ HF HG).
  intros i j HI HJ. destruct(environment_lt_cases M i (code_numeral M 1)) as[Hin|Hout].
  - change(coding_lt M i (succM M(zeroM M))) in Hin.
    apply coding_lt_succ_cases in Hin. destruct Hin as[Hbad|E];[exfalso;exact(coding_not_lt_zero M i Hbad)|].
    subst i. pose proof(renaming_lookup_functional M _ _ _ _ _ j _ HJ (source_native_k_upshift_zero M)) as E.
    subst j. apply coding_zero_lt_succ.
  - apply renaming_lookup_outside in HJ;[|exact Hout]. subst j.
    change(coding_lt M (addM M i (succM M(zeroM M)))(succM M(succM M k))).
    rewrite Arithmetic.add_comm,Arithmetic.add_succ,Arithmetic.add_zero.
    exact(proj2(coding_lt_succ_cancel M i (succM M k)) HI).
Qed.
Theorem source_native_k_upshift_finite M (phi:sf_form) :
  source_native_k_upshift M (code_numeral M(sf_encode phi))(code_numeral M(sf_encode phi[up ↑])).
Proof.
  apply(proj2(numerical_renaming_substitution M _ _ _ _ _ _)).
  apply(fixed_source_substitution M (fun _=>zeroM M) phi (up ↑)
    (zeroM M)(zeroM M)(code_numeral M 1)(addM M(code_numeral M 1)(code_numeral M 1)) _ _).
  - intro i. exact(proj1(renaming_substitution_lookup M _ _ _ _ _ _)(source_native_k_upshift_fixed_lookup M i)).
  - apply source_formula_numeral_graph.
  - apply source_formula_numeral_graph.
Qed.

Print Assumptions source_native_k_upshift_bound.
Print Assumptions source_native_k_upshift_finite.
