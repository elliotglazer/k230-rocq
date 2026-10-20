(** Free-name bounds for open PCf ordinal-witness bodies. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  SourceDomainInstances SourceOrdinalPredicate SourcePieceConjunctionBounds SourcePieceBoundBody.
Unset Implicit Arguments.

Theorem source_pcf_bound_body_bounded M domain level sb sc n g X d body k:
  source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
  source_piece_table_valid M sb sc n ->coding_lt M g k ->coding_lt M X k ->coding_lt M d k ->
  source_pcf_bound_body M domain level sb sc n g X d body ->source_bounded M body k.
Proof.
  intros HD HL HV HG HX HDk(ordinal&member&pc&left&HO&HM&HPC&HLeft&HBody).
  pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)d ordinal k
    (source_ordinal_predicate_bounded M)HDk HO) as BOrd.
  pose proof(proj2(source_bounded_accept_atom M SFMember g d member k(or_introl eq_refl)HM)(conj HG HDk)) as BMember.
  pose proof(source_piece_conjunction_bounded M n domain level sb sc d X pc k HD HL HV HDk HX HPC) as BPc.
  pose proof(proj2(source_bounded_accept_binary M SFAnd ordinal member left k(or_introl eq_refl)HLeft)(conj BOrd BMember)) as BLeft.
  exact(proj2(source_bounded_accept_binary M SFAnd left pc body k(or_introl eq_refl)HBody)(conj BLeft BPc)).
Qed.

Print Assumptions source_pcf_bound_body_bounded.
