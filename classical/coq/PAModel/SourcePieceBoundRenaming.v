(** Capture-avoiding transport of the exact existential PCf-bound goal. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded NumericalRenamingMaps NumericalRenaming
  NumericalContextRenaming SourceQuantifierRules SourceRenamingIdentity SourceOrdinalPredicate SourcePieceBoundGoal
  SourcePieceConjunctionBounds SourcePieceConjunctionRenaming.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.

Theorem source_pcf_bound_goal_renaming M domain level sb sc n g X f rb rc rn delta h Y out:
  source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
  source_piece_table_valid M sb sc n ->source_pcf_bound_goal M domain level sb sc n g X f ->
  numerical_renaming M f rb rc rn delta out ->renaming_lookup M rb rc rn delta g h ->
  renaming_lookup M rb rc rn delta X Y ->source_pcf_bound_goal M domain level sb sc n h Y out.
Proof.
  intros HD HL HV(pc&member&left&body&HPC&HM&HLeft&HBody&HEx)HR HNameG HNameX.
  destruct(proj1(numerical_renaming_quantifier M false body f rb rc rn delta out HEx)HR)
    as(ab&ac&an&body'&HMap&HRBody&HEx').
  destruct(proj1(numerical_renaming_binary M SFAnd left pc body ab ac an delta body'(or_introl eq_refl)HBody)HRBody)
    as(left'&pc'&HRLeft&HRPc&HBody').
  destruct(proj1(numerical_renaming_binary M SFAnd(source_ordinal_predicate_code M)member left ab ac an delta left'
    (or_introl eq_refl)HLeft)HRLeft) as(ordinal'&member'&HROrd&HRMember&HLeft').
  pose proof(numerical_renaming_lift_fixes_domain M(source_ordinal_predicate_code M)rb rc rn delta ab ac an
    (source_ordinal_predicate_bounded M)HMap) as HOrdSelf.
  pose proof(numerical_renaming_functional M(source_ordinal_predicate_code M)ab ac an delta ordinal'
    (source_ordinal_predicate_code M)HROrd HOrdSelf) as E. subst ordinal'.
  pose proof(source_piece_conjunction_renaming M n domain level sb sc(zeroM M)(succM M X)pc ab ac an delta
    (zeroM M)(succM M Y)pc' HD HL HV HPC HRPc(proj1(proj2 HMap))
    (proj2(proj2 HMap)X Y HNameX)) as HPC'.
  destruct(proj1(numerical_renaming_member M(succM M g)(zeroM M)member ab ac an delta member' HM)HRMember)
    as(u&v&HU&HV'&HMember').
  pose proof(renaming_lookup_functional M ab ac an delta(succM M g)u(succM M h)HU
    (proj2(proj2 HMap)g h HNameG)) as E. subst u.
  pose proof(renaming_lookup_functional M ab ac an delta(zeroM M)v(zeroM M)HV'(proj1(proj2 HMap))) as E. subst v.
  exists pc',member',left',body'. auto.
Qed.

Theorem source_pcf_bound_goal_shift M domain level sb sc n g X f out:
  source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
  source_piece_table_valid M sb sc n ->source_pcf_bound_goal M domain level sb sc n g X f ->
  source_formula_shift M f out ->source_pcf_bound_goal M domain level sb sc n(succM M g)(succM M X)out.
Proof.
  intros HD HL HV HF HR.
  apply(source_pcf_bound_goal_renaming M domain level sb sc n g X f(zeroM M)(zeroM M)(zeroM M)
    (code_numeral M 1)(succM M g)(succM M X)out HD HL HV HF HR);
    apply context_shift_lookup;reflexivity.
Qed.

Print Assumptions source_pcf_bound_goal_renaming.
Print Assumptions source_pcf_bound_goal_shift.
