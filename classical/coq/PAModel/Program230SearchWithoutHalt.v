(** The halt contract is actual; only the nonhalting action implementation remains. *)
From PAModel Require Import Model Program230HaltingSentence Program230SearchRealization
 Program230SearchComparison Program230SearchHalt.
Unset Implicit Arguments.
Theorem p230_counter_search_equivalence_from_normal M:
 p230_normal_search_macro M ->
 (p230_counter_halting M <-> p230_numerical_search_halts M).
Proof.
 intro Hnormal;exact(p230_counter_numerical_search_equivalence_from_macros M Hnormal
  (p230_actual_halt_search_macro M)).
Qed.
Print Assumptions p230_counter_search_equivalence_from_normal.
