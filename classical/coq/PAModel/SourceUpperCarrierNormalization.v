(** Move the carrier off the output role and recover the exact original
    canonical output-root recipe. The original predicate remains arbitrary. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes
  SourceBounded SourceFiniteCutoffShift SourceNativeKRecipes SourceNativeKShifts
  SourceEmittedClosureRecipe SourceEmittedParameterInsertion SourceBoundedOutputRoot
  SourceCarrierRenaming SourceCutoffReopening SourceRoleReopening NumericalRenamingMaps NumericalRenaming.
Unset Implicit Arguments.

Theorem source_upper_recipe_carrier_normalization M phi phi' n fresh rb rc rn before after :
  source_bounded M phi (succM M (succM M n)) ->source_cutoff_shift M 2 phi phi' ->
  coding_lt M (succM M (succM M n)) fresh ->
  renaming_lookup M rb rc rn (zeroM M) fresh (zeroM M) ->
  carrier_positive_fixes M fresh rb rc rn ->
  source_trace_output_root_recipe M phi' fresh (code_numeral M 1) before ->
  source_upper_conclusion_recipe M phi after ->
  numerical_renaming M before rb rc rn (zeroM M) after.
Proof.
  intros HP HS HBound HFresh HFix
    (ab&ac&value&emitted&member&root&pair&HMap&HValue&HEmitted&HMember&HRoot&HPair&HBefore)
    (shiftphi&h&shifted&atom&root'&pair'&HPhiShift&HEm&HUp&HAtom&HRoot'&HPair'&HAfter).
  pose proof (source_emitted_closure_parameter_insertion M phi phi' h emitted
    (succM M (succM M n)) HP HS HEm HEmitted) as HEUp.
  pose proof (numerical_renaming_functional M h _ _ _ _ emitted shifted HEUp HUp) as E.
  subst emitted.
  destruct (renaming_lift_total M rb rc rn (zeroM M)) as [b [c [l HL]]].
  pose proof (source_cutoff_two_reopening M phi phi' ab ac value (succM M (succM M n))
    HP HS HValue) as HV.
  pose proof (source_reopened_carrier_to_shift M phi value shiftphi (succM M (succM M n))
    fresh ab ac rb rc rn b c l HP HBound HMap HV HPhiShift HFresh HFix HL) as RV.
  pose proof (source_emitted_closure_recipe_bound M phi h n HP HEm) as HBoundH.
  pose proof (source_native_upshift_carrier_fixed M h shifted (succM M (succM M n)) fresh
    rb rc rn b c l HBoundH HBound HUp HFix HL) as RH.
  assert (RA:numerical_renaming M member b c l (zeroM M) atom).
  { apply (proj2 (numerical_renaming_member M (succM M fresh)(zeroM M) member
      b c l (zeroM M) atom HMember)).
    exists (code_numeral M 1),(zeroM M). split.
    - exact (proj2 (renaming_lift_tail M rb rc rn (zeroM M) b c l fresh (zeroM M) HL) HFresh).
    - split;[exact (proj2 (renaming_lift_head M rb rc rn (zeroM M) b c l (zeroM M) HL) eq_refl)|exact HAtom]. }
  assert (RR:numerical_renaming M root b c l (zeroM M) root').
  { apply (proj2 (numerical_renaming_binary M SFImpl value member root b c l (zeroM M) root'
      (or_intror (or_intror eq_refl)) HRoot)). exists shiftphi,atom. auto. }
  assert (RP:numerical_renaming M pair b c l (zeroM M) pair').
  { apply (proj2 (numerical_renaming_binary M SFAnd root shifted pair b c l (zeroM M) pair'
      (or_introl eq_refl) HPair)). exists root',shifted. auto. }
  apply (proj2 (numerical_renaming_quantifier M false pair before rb rc rn (zeroM M) after HBefore)).
  exists b,c,l,pair'. auto.
Qed.

Print Assumptions source_upper_recipe_carrier_normalization.
