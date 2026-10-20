(** Functionality of a binary relation is a literal source sentence. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 SourceRecursionBinaryInstance SourceRecursionBinaryTransport SourceRecursionFunctionality SourceFunctionalityShells
 SourceClosedShift SourceQuantifierRules.
Unset Implicit Arguments.
Theorem source_rec_functionality_closed M phi out:
 source_bounded M phi(code_numeral M 2) ->source_rec_functionality M phi out ->source_bounded M out(zeroM M).
Proof.
 intros BP(a&b&HA&HB&HF).
 pose proof(source_rec_binary_rep M phi a SchemaRenamingDescriptors.RepA(or_introl eq_refl)BP HA)as HBA.
 pose proof(source_rec_binary_rep M phi b SchemaRenamingDescriptors.RepB(or_intror eq_refl)BP HB)as HBB.
 pose proof(source_rec_binary_bounded M phi(code_numeral M 2)(code_numeral M 1)a(code_numeral M 3)BP
  (coding_lt_succ M(code_numeral M 2))(proj2(coding_lt_succ_cancel M(zeroM M)(code_numeral M 2))(coding_zero_lt_succ M(code_numeral M 1)))HBA)as BA.
 pose proof(source_rec_binary_bounded M phi(code_numeral M 2)(zeroM M)b(code_numeral M 3)BP
  (coding_lt_succ M(code_numeral M 2))(coding_zero_lt_succ M(code_numeral M 2))HBB)as BB.
 destruct(sf_relation_total M SFEqual(code_numeral M 1)(zeroM M))as(equal&HE).
 destruct(source_functionality_shell M a b equal out HE HF)as(rhs&point&p1&p2&HR&HP&H1&H2&H3).
 pose proof(proj2(source_bounded_accept_atom M SFEqual _ _ equal(code_numeral M 3)(or_intror eq_refl)HE)
  (conj(proj2(coding_lt_succ_cancel M(zeroM M)(code_numeral M 2))(coding_zero_lt_succ M(code_numeral M 1)))(coding_zero_lt_succ M(code_numeral M 2))))as BE.
 pose proof(proj2(source_bounded_accept_binary M SFImpl b equal rhs(code_numeral M 3)(or_intror(or_intror eq_refl))HR)(conj BB BE))as BR.
 pose proof(proj2(source_bounded_accept_binary M SFImpl a rhs point(code_numeral M 3)(or_intror(or_intror eq_refl))HP)(conj BA BR))as BPoint.
 pose proof(proj2(source_bounded_accept_unary M SFAll point p1(code_numeral M 2)(or_introl eq_refl)H1)BPoint)as B1.
 pose proof(proj2(source_bounded_accept_unary M SFAll p1 p2(code_numeral M 1)(or_introl eq_refl)H2)B1)as B2.
 exact(proj2(source_bounded_accept_unary M SFAll p2 out(zeroM M)(or_introl eq_refl)H3)B2).
Qed.
Theorem source_rec_functionality_shift M phi out:
 source_bounded M phi(code_numeral M 2) ->source_rec_functionality M phi out ->source_formula_shift M out out.
Proof. intros BP HO. exact(source_closed_shift_self M out(source_rec_functionality_closed M phi out BP HO)). Qed.
Print Assumptions source_rec_functionality_closed.
Print Assumptions source_rec_functionality_shift.
