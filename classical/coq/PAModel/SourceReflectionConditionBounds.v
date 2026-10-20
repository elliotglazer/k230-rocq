(** Cond has exactly its two displayed ordinal-name roles, for valid internal piece tables. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
  SourceDomainInstances SourceHierarchySyntax SourcePieceConjunctionBounds SourceReflectionCondition.
Unset Implicit Arguments.

Theorem source_reflection_condition_bounded M domain level ordinal sb sc n x y out k :
  source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
  source_bounded M ordinal(code_numeral M 1) ->source_piece_table_valid M sb sc n ->
  coding_lt M x k ->coding_lt M y k ->source_reflection_condition M domain level ordinal sb sc n x y out ->
  source_bounded M out k.
Proof.
  intros HD HL HO HV HX HY(ord&member&lev&pc&point&all&both&HOrd&HMember&HLevel&HPC&HPoint&HAll&HBoth&HOut).
  pose proof(source_domain_instance_bound M ordinal x ord k HO HX HOrd) as BOrd.
  assert(BMember:source_bounded M member k).
  { exact(proj2(source_bounded_accept_atom M SFMember x y member k(or_introl eq_refl)HMember)(conj HX HY)). }
  pose proof(source_LL_instance_bounded M(succM M x)(zeroM M)lev(succM M k)
    (proj2(coding_lt_succ_cancel M x k)HX)(coding_zero_lt_succ M k)HLevel) as BLevel.
  pose proof(source_piece_conjunction_bounded M n domain level sb sc(succM M y)(zeroM M)pc(succM M k)
    HD HL HV(proj2(coding_lt_succ_cancel M y k)HY)(coding_zero_lt_succ M k)HPC) as BPC.
  assert(BPoint:source_bounded M point(succM M k)).
  { exact(proj2(source_bounded_accept_binary M SFImpl lev pc point _(or_intror(or_intror eq_refl))HPoint)(conj BLevel BPC)). }
  pose proof(proj2(source_bounded_accept_unary M SFAll point all k(or_introl eq_refl)HAll)BPoint) as BAll.
  assert(BBoth:source_bounded M both k).
  { exact(proj2(source_bounded_accept_binary M SFAnd member all both k(or_introl eq_refl)HBoth)(conj BMember BAll)). }
  exact(proj2(source_bounded_accept_binary M SFImpl ord both out k(or_intror(or_intror eq_refl))HOut)(conj BOrd BBoth)).
Qed.

Print Assumptions source_reflection_condition_bounded.
