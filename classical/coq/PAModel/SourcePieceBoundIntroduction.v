(** Ordinary source ExI introduces a PCf bound at any actual named ordinal
    witness. The body instantiation is computed and normalized internally. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
  NumericalContexts NumericalSourceFull NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation
  SourceUnarySubstitution SourceDomainInstances SourceOrdinalPredicate SubstitutionSource SourcePieceBoundGoal
  SourcePieceConjunction SourcePieceConjunctionBounds SourcePieceConjunctionSubstitution.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.

Theorem source_full_pcf_bound_intro M b c l domain level sb sc n g X goal d ordinal member pc k:
  source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
  source_piece_table_valid M sb sc n ->coding_lt M g k ->coding_lt M X k ->coding_lt M d k ->
  context_bounded M b c l k ->source_pcf_bound_goal M domain level sb sc n g X goal ->
  numerical_instantiation M(source_ordinal_predicate_code M)d ordinal ->sf_relation M SFMember g d member ->
  source_piece_conjunction M domain level sb sc n d X pc ->
  source_full_prv M b c l ordinal ->source_full_prv M b c l member ->source_full_prv M b c l pc ->
  source_full_prv M b c l goal.
Proof.
  intros HD HL HV HG HX HDk HC HGoal HOrd HMember HPc POrd PMember PPc.
  pose proof(source_pcf_bound_goal_bounded M domain level sb sc n g X goal k HD HL HV HG HX HGoal) as BGoal.
  destruct HGoal as(oldPc&oldMember&oldLeft&body&HOldPc&HOldMember&HOldLeft&HBody&HEx).
  destruct(sf_relation_total M SFAnd ordinal member) as(left&HLeft).
  destruct(sf_relation_total M SFAnd left pc) as(instance&HInstance).
  destruct(substitution_singleton_total M d) as(rb&rc&HHead&HTail).
  pose proof(source_domain_instance_substitution_graph M(source_ordinal_predicate_code M)(zeroM M)
    (source_ordinal_predicate_code M)rb rc(code_numeral M 1)(zeroM M)d ordinal(source_ordinal_predicate_bounded M)
    (source_domain_instance_zero M(source_ordinal_predicate_code M)(source_ordinal_predicate_bounded M))HHead HOrd) as HOrdSub.
  assert(HMemberSub:numerical_substitution M oldMember rb rc(code_numeral M 1)(zeroM M)member).
  { apply(proj2(numerical_substitution_member M(succM M g)(zeroM M)oldMember rb rc(code_numeral M 1)(zeroM M)
      member HOldMember)). exists g,d. split;[apply substitution_singleton_tail|]. auto. }
  destruct(numerical_substitution_total M oldPc rb rc(code_numeral M 1)(zeroM M)) as(pc'&HPcSub).
  pose proof(source_piece_conjunction_substitution M n domain level sb sc(zeroM M)(succM M X)oldPc
    rb rc(code_numeral M 1)(zeroM M)d X pc' HD HL HV HOldPc HPcSub HHead
    (substitution_singleton_tail M rb rc X)) as HPc'.
  pose proof(source_piece_conjunction_functional M domain level sb sc n d X pc' pc HPc' HPc) as E. subst pc'.
  assert(HLeftSub:numerical_substitution M oldLeft rb rc(code_numeral M 1)(zeroM M)left).
  { apply(proj2(numerical_substitution_binary M SFAnd(source_ordinal_predicate_code M)oldMember oldLeft
      rb rc(code_numeral M 1)(zeroM M)left(or_introl eq_refl)HOldLeft)).
    exists ordinal,member. repeat split;assumption. }
  assert(HInst:numerical_instantiation M body d instance).
  { exists rb,rc. split;[exact HHead|].
    apply(proj2(numerical_substitution_binary M SFAnd oldLeft oldPc body rb rc(code_numeral M 1)(zeroM M)
      instance(or_introl eq_refl)HBody)). exists left,pc. repeat split;assumption. }
  pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)d ordinal k
    (source_ordinal_predicate_bounded M)HDk HOrd) as BOrd.
  pose proof(proj2(source_bounded_accept_atom M SFMember g d member k(or_introl eq_refl)HMember)(conj HG HDk)) as BMember.
  pose proof(source_piece_conjunction_bounded M n domain level sb sc d X pc k HD HL HV HDk HX HPc) as BPc.
  pose proof(proj2(source_bounded_accept_binary M SFAnd ordinal member left k(or_introl eq_refl)HLeft)(conj BOrd BMember)) as BLeft.
  pose proof(proj2(source_bounded_accept_binary M SFAnd left pc instance k(or_introl eq_refl)HInstance)(conj BLeft BPc)) as BInstance.
  apply(full_source_ExI M b c l body goal d instance(ex_intro _ k(conj BGoal HC)));[|exact HEx|exact HInst].
  exact(full_source_CI M b c l left pc instance(ex_intro _ k(conj BInstance HC))
    (full_source_CI M b c l ordinal member left(ex_intro _ k(conj BLeft HC))POrd PMember HLeft)PPc HInstance).
Qed.

Print Assumptions source_full_pcf_bound_intro.
