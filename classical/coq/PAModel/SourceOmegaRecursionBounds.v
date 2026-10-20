(** Bounds of the literal fixed omega recursion witness formula. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 SourceOmegaRecursionFixed SourceOmegaRecursionShell SourceRecursionInductionBounds
 SourceRecursionStructureBounds SourceRecursionPrimitiveShifts FixedSourceBounds.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Theorem source_omega_recursion_body_bounded M:
 source_bounded M(source_omega_recursion_body_code M)(code_numeral M 2).
Proof.
 destruct(source_omega_recursion_body_shell M)as(member&total&injective&nonzero&inductive&tail1&tail2&tail3&HM&HT&HI&HN&HD&H3&H2&H1&H0).
 assert(B0:coding_lt M(code_numeral M 0)(code_numeral M 2))by(apply(proj2(fixed_source_numeral_lt_iff M 0 2));lia).
 assert(B1:coding_lt M(code_numeral M 1)(code_numeral M 2))by(apply(proj2(fixed_source_numeral_lt_iff M 1 2));lia).
 pose proof(source_rec_nonzero_bounded M(code_numeral M 0)(code_numeral M 1)nonzero(code_numeral M 2)B0 B1 HN)as BN.
 pose proof(source_rec_induction_bounded M(code_numeral M 0)(code_numeral M 1)inductive(code_numeral M 2)B0 B1 HD)as BD.
 pose proof(source_rec_injectivity_bounded M(code_numeral M 1)injective(code_numeral M 2)B1 HI)as BI.
 pose proof(source_rec_totality_bounded M(code_numeral M 1)total(code_numeral M 2)B1 HT)as BT.
 pose proof(proj2(source_bounded_accept_atom M SFMember _ _ member(code_numeral M 2)(or_introl eq_refl)HM)(conj B0 B1))as BM.
 pose proof(proj2(source_bounded_accept_binary M SFAnd nonzero inductive tail3(code_numeral M 2)(or_introl eq_refl)H3)(conj BN BD))as BT3.
 pose proof(proj2(source_bounded_accept_binary M SFAnd injective tail3 tail2(code_numeral M 2)(or_introl eq_refl)H2)(conj BI BT3))as BT2.
 pose proof(proj2(source_bounded_accept_binary M SFAnd total tail2 tail1(code_numeral M 2)(or_introl eq_refl)H1)(conj BT BT2))as BT1.
 exact(proj2(source_bounded_accept_binary M SFAnd member tail1 _ (code_numeral M 2)(or_introl eq_refl)H0)(conj BM BT1)).
Qed.
Theorem source_omega_recursion_inner_bounded M:
 source_bounded M(source_omega_recursion_inner_code M)(code_numeral M 1).
Proof. exact(proj2(source_bounded_accept_unary M SFEx _ _ (code_numeral M 1)(or_intror eq_refl)(source_omega_recursion_inner_graph M))(source_omega_recursion_body_bounded M)). Qed.
Theorem source_omega_recursion_closed M:
 source_bounded M(source_omega_recursion_code M)(zeroM M).
Proof. exact(proj2(source_bounded_accept_unary M SFEx _ _ (zeroM M)(or_intror eq_refl)(source_omega_recursion_outer_graph M))(source_omega_recursion_inner_bounded M)). Qed.
Print Assumptions source_omega_recursion_body_bounded.
Print Assumptions source_omega_recursion_inner_bounded.
Print Assumptions source_omega_recursion_closed.
