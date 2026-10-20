From PAModel Require Import Model FiniteCoding FiniteCRT SetFormulaCodes SourceBounded SourceRecursionAgreementSubset.
Unset Implicit Arguments.
Theorem source_rec_subset_chart_bounded M f g N X out k:
 coding_lt M f k ->coding_lt M g k ->coding_lt M N k ->coding_lt M X k ->source_rec_subset_chart M f g N X out ->source_bounded M out k.
Proof.
 intros BF BG BN BX(point&HP&HA). apply(proj2(source_bounded_accept_unary M SFAll point out k(or_introl eq_refl)HA)).
 exact(source_rec_subset_point_bounded M(succM M f)(succM M g)(succM M N)(succM M X)(zeroM M)point(succM M k)
  (proj2(coding_lt_succ_cancel M f k)BF)(proj2(coding_lt_succ_cancel M g k)BG)(proj2(coding_lt_succ_cancel M N k)BN)
  (proj2(coding_lt_succ_cancel M X k)BX)(coding_zero_lt_succ M k)HP).
Qed.
Print Assumptions source_rec_subset_chart_bounded.
