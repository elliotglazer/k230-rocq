(** Actual shift and witness instantiation for the one-level reflection
    condition. No proof-preservation or graph-commutation premise remains. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SourceBounded SourceBoundMonotone
  NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation NumericalRenaming RenamingSubstitution
  SourceQuantifierRules SourceFiniteCutoffShift SourceD0At SourceD0Substitution
  SourceCutoffSingletonCancellation.
Unset Implicit Arguments.

Theorem source_d0_at_shift M domain phi phi' d out shifted k :
  source_bounded M domain(code_numeral M 1) ->source_bounded M phi k ->
  source_cutoff_shift M 1 phi phi' ->source_d0_at M domain phi d out ->
  source_formula_shift M out shifted ->source_d0_at M domain phi'(succM M d) shifted.
Proof.
  intros HD HB HC HG HS.
  destruct(source_d0_at_total M domain phi'(succM M d)) as (next&HN).
  destruct HC as (ab&ac&an&(u&v&m&(EU&EV&EM)&HL)&HP).
  subst u v m.
  pose proof(source_d0_at_substitution M domain phi phi' d(succM M d) out next k
    (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1) ab ac an HD HB HL HP
    (source_cutoff_shift_base_lookup M d) HG HN) as HSub.
  pose proof(proj2(numerical_renaming_empty_substitution M out(zeroM M)(zeroM M)
    (code_numeral M 1) next) HSub) as HR.
  pose proof(numerical_renaming_functional M out(zeroM M)(zeroM M)(zeroM M)
    (code_numeral M 1) next shifted HR HS) as E. now subst next.
Qed.

Theorem source_d0_at_witness_instantiation M domain phi phi' body result t k :
  source_bounded M domain(code_numeral M 1) ->source_bounded M phi k ->
  source_cutoff_shift M 1 phi phi' ->
  source_d0_at M domain phi'(zeroM M) body ->source_d0_at M domain phi t result ->
  numerical_instantiation M body t result.
Proof.
  intros HD HB HC HBody HResult.
  destruct(substitution_singleton_total M t) as (b&c&HHead&HTail).
  destruct(substitution_lift_total M b c(code_numeral M 1)(zeroM M)) as (ab&ac&an&HL).
  pose proof(source_cutoff_one_singleton_lift_cancel M phi phi' k b c ab ac an HB HC HL) as HMatrix.
  assert(HB':source_bounded M phi'(succM M(succM M k))).
  { apply(source_cutoff_shift_bounded M 1 phi phi' k);[|exact HC].
    exact(source_bounded_monotone M phi k(succM M k) HB
      (coding_lt_trans M k(succM M k)(succM M(succM M k))
        (coding_lt_succ M k)(coding_lt_succ M(succM M k)))). }
  exists b,c. split;[exact HHead|].
  apply(source_d0_at_substitution M domain phi' phi(zeroM M) t body result(succM M(succM M k))
    b c(code_numeral M 1)(zeroM M) ab ac an HD HB' HL HMatrix HHead HBody HResult).
Qed.

Print Assumptions source_d0_at_shift.
Print Assumptions source_d0_at_witness_instantiation.
