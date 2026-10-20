(** Uniform bounds for the finite membership shell around arbitrary NumF codes. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes FixedSourceBounds
 SourceBounded SourceBoundMonotone SourceNumFClosureSyntax.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Theorem source_numf_bound_to_six M f n :(n<=6)%nat ->source_bounded M f(code_numeral M n) ->source_bounded M f(code_numeral M 6).
Proof.
 intros HN HF. apply(source_bounded_monotone M f(code_numeral M n)(code_numeral M 6)HF).
 exact(proj2(fixed_source_numeral_lt_iff M n 7)ltac:(lia)).
Qed.
Theorem source_numf_member_shell_bounded M f r body ex :source_bounded M f(code_numeral M 1) ->
 source_numf_member_shell M f r body ex ->source_bounded M body(code_numeral M(S r)) /\source_bounded M ex(code_numeral M r).
Proof.
 intros HF(HB&HE).
 assert(BF:source_bounded M f(code_numeral M(S r))).
 { apply(source_bounded_monotone M f(code_numeral M 1)(code_numeral M(S r))HF).
   apply coding_lt_succ_cancel,coding_zero_lt_succ. }
 assert(BM:source_bounded M(source_numf_closure_member M r)(code_numeral M(S r))).
 { apply source_numf_closure_member_bounded;[apply coding_zero_lt_succ|apply coding_lt_succ]. }
 pose proof(proj2(source_bounded_accept_binary M SFAnd f _ body(code_numeral M(S r))(or_introl eq_refl)HB)(conj BF BM))as BB.
 split;[exact BB|exact(proj2(source_bounded_accept_unary M SFEx body ex(code_numeral M r)(or_intror eq_refl)HE)BB)].
Qed.
Print Assumptions source_numf_bound_to_six.
Print Assumptions source_numf_member_shell_bounded.
