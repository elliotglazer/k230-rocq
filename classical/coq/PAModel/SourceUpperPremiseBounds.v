(** Finite source bounds for the exact trace and closure premises used
    by carrier normalization. No proof-existence premise is required. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  SetFormulaCodes SetSchemaConstructors SchemaConstructorBounds SourceBounded SourceRenamingBounds
  SourceUpperTraceRecipe SourceUpperTraceProfile SourceFiniteCutoffShift SourceUpperWitnessRecipes
  SourceWitnessMatrixSpecialization SourceTraceMatrixAlignment SourceUpperTraceFrame
  SourceSubsetClosedPoint SourceSubsetClosedShift SourceFiniteParameterProofs SourceFiniteParameters
  SourceNumeralLift SourceUnaryParameters NumericalInstantiation SourceSubstitutionBounds NumericalRenaming NumericalRenamingMaps SourceBoundMonotone.
From FOL.Tennenbaum Require Import Peano.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
Unset Implicit Arguments.

Theorem source_upper_trace_profile_bound M phi profile n :
  source_bounded M phi (succM M (succM M n)) ->source_upper_trace_profile M phi profile ->
  source_bounded M profile (succM M (succM M n)).
Proof.
  intros HP (trace&theta&HT&HS&HO).
  pose proof (source_upper_trace_bounded M phi trace n HP HT) as HB.
  pose proof (source_cutoff_shift_bounded M 1 trace theta (succM M n) HB HS) as HTheta.
  assert (HBound:schema_expression_bound M (fun _=>theta)(E_upper_trace_profile (CEvar 0))
      (succM M (succM M n))).
  { unfold E_upper_trace_profile,E_sf_all,E_sf_iff,E_sf_mem.
    repeat schema_constructor_bound;try schema_small_index;exact HTheta. }
  exact (HBound profile HO).
Qed.

Theorem source_upper_witness_carrier_bound M phi witness n :
  source_bounded M phi (succM M (succM M n)) ->
  source_upper_witness_closed_recipe M phi (code_numeral M 1)(zeroM M) witness ->
  source_bounded M witness (succM M n).
Proof.
  intros HP (mat&HM&HO).
  assert (BMat:source_bounded M mat (succM M (succM M (succM M n)))).
  { apply (numerical_renaming_preserves_bound M phi (code_numeral M 4)(code_numeral M 1)
      (code_numeral M 2)(code_numeral M 1) mat (succM M (succM M n))
      (succM M (succM M (succM M n))) HP HM).
    intros i j HI HJ.
    destruct (@Peano.zero_or_succ (carrier M)(raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) i) as [->|[i' ->]].
    - pose proof (renaming_lookup_functional M _ _ _ _ _ j (zeroM M) HJ
        (proj1 (source_identity_delta_prefix M (code_numeral M 1)))) as E. subst j. apply coding_zero_lt_succ.
    - destruct (@Peano.zero_or_succ (carrier M)(raw_interpretation M)
        (fun ax H rho=>axioms M ax rho H) i') as [->|[i'' ->]].
      + pose proof (renaming_lookup_functional M _ _ _ _ _ j (code_numeral M 1) HJ
          (proj2 (source_identity_delta_prefix M (code_numeral M 1)))) as E. subst j.
        apply coding_lt_succ_cancel,coding_zero_lt_succ.
      + apply (proj1 (renaming_lookup_outside M _ _ _ _ _ _ (source_two_succ_not_lt_two M i''))) in HJ.
        cbn [code_numeral] in HJ. rewrite Arithmetic.add_comm,Arithmetic.add_succ,Arithmetic.add_zero in HJ. subst j.
        apply coding_lt_succ_cancel. exact HI. }
  destruct (source_upper_witness_closed_shell M mat (zeroM M) witness HO)
    as (guard&member&pair&some&bounded&request&point&HG&HMemb&HAnd&HSome&HBound&HReq&HImp&HAll).
  apply (proj2 (source_bounded_accept_unary M SFAll point witness (succM M n)(or_introl eq_refl) HAll)).
  apply (proj2 (source_bounded_accept_binary M SFImpl guard request point (succM M (succM M n))
    (or_intror (or_intror eq_refl)) HImp)). split.
  - apply (proj2 (source_bounded_accept_atom M SFMember (zeroM M)(code_numeral M 1) guard
      (succM M (succM M n))(or_introl eq_refl) HG)).
    split;[apply coding_zero_lt_succ|apply coding_lt_succ_cancel,coding_zero_lt_succ].
  - apply (proj2 (source_bounded_accept_binary M SFImpl some bounded request (succM M (succM M n))
      (or_intror (or_intror eq_refl)) HReq)). split.
    + exact (proj2 (source_bounded_accept_unary M SFEx mat some (succM M (succM M n))
        (or_intror eq_refl) HSome) BMat).
    + apply (proj2 (source_bounded_accept_unary M SFEx pair bounded (succM M (succM M n))
        (or_intror eq_refl) HBound)).
      apply (proj2 (source_bounded_accept_binary M SFAnd member mat pair (succM M (succM M (succM M n)))
        (or_introl eq_refl) HAnd)). split;[|exact BMat].
      apply (proj2 (source_bounded_accept_atom M SFMember (zeroM M)(code_numeral M 2) member
        (succM M (succM M (succM M n)))(or_introl eq_refl) HMemb)).
      split;[apply coding_zero_lt_succ|apply (proj2 (coding_lt_succ_cancel M (code_numeral M 1)(succM M (succM M n))));apply (proj2 (coding_lt_succ_cancel M (zeroM M)(succM M n)));apply coding_zero_lt_succ].
Qed.

Theorem source_subset_carrier_bound M f :source_subset_closed_graph M (zeroM M) f ->
  source_bounded M f (code_numeral M 1).
Proof.
  intro HF.
  pose proof (source_unary_parameter_instantiation M (source_point_subset_closed $0)
    source_three_parameter_names (fun _=>zeroM M)(zeroM M) f
    source_point_subset_closed_bound eq_refl HF) as HI.
  pose proof (proj2 (source_formula_numeral_bounded M (source_point_subset_closed $0) 1)
    source_point_subset_closed_bound) as HB.
  apply (numerical_instantiation_bounded M (code_numeral M(sf_encode(source_point_subset_closed $0)))
    (zeroM M) f (code_numeral M 1));[|apply coding_zero_lt_succ|exact HI].
  apply (source_bounded_monotone M _ (code_numeral M 1)(code_numeral M 2) HB).
  apply coding_lt_succ_cancel,coding_zero_lt_succ.
Qed.

Print Assumptions source_upper_trace_profile_bound.
Print Assumptions source_upper_witness_carrier_bound.
Print Assumptions source_subset_carrier_bound.
