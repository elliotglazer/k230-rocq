(** Fixed support bounds in the arbitrary-code numeral comparison proof. *)
From PAModel Require Import Model FiniteCoding FixedSourceBounds CodeExpressions SetFormulaCodes SourceNumeralLift
 SourceBounded SourceBoundMonotone SourceDefinabilityPrimitives SourceFiniteCutoffShift
 SourceImplicationAllShift SourceNumFClosureFiniteShells SourceNumFUniqueSyntax SourceNumFUniqueFiniteShells.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Theorem source_numf_compare_successor_bounds M :
 source_bounded M(numf_closure_succ_shift_code M)(code_numeral M 3) /\
 source_bounded M(code_numeral M(sf_encode numf_successor03))(code_numeral M 4).
Proof.
 destruct(source_numf_successor_cutoffs M)as(H12&H23).
 pose proof(source_cutoff_shift_bounded M 1 _ _(code_numeral M 1)(numerical_def_successor_bound M)H12)as B02.
 split;[exact(source_shift_bound M _ _(code_numeral M 2)(numerical_def_successor_bound M)(source_numf_closure_succ_shift M))|].
 exact(source_cutoff_shift_bounded M 1 _ _(code_numeral M 2)B02 H23).
Qed.
Theorem source_numf_equal_bound6 M a b :(a<6)%nat ->(b<6)%nat ->source_bounded M(numf_equal_code M a b)(code_numeral M 6).
Proof.
 intros HA HB. exact(proj2(source_bounded_accept_atom M SFEqual(code_numeral M a)(code_numeral M b)_(code_numeral M 6)
  (or_intror eq_refl)(sf_make_numeral M SFEqual a b))
  (conj(proj2(fixed_source_numeral_lt_iff M a 6)HA)(proj2(fixed_source_numeral_lt_iff M b 6)HB))).
Qed.
Print Assumptions source_numf_compare_successor_bounds.
Print Assumptions source_numf_equal_bound6.
