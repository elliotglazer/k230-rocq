(** Keep a local condition outside a guarded universal proof map. All
    formula codes may be nonstandard; the condition's genuine source shift
    is checked explicitly. This is a pure source-calculus proof. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalContexts NumericalEnvironments NumericalContextRenaming NumericalSourceFull SourceProofRenaming
  SourceQuantifierRules SourceUniversalDistribution SourceImplicationAllShift SourceContextTransport
  SourceContextProofHelpers SourceLeastOrdinalWitness SourceDerivedRules.
Unset Implicit Arguments.

Theorem source_conditional_universal_map M condition shifted a b guard ab point qpoint ga gb qa qb qmap cond out k :
  source_bounded M condition k ->source_formula_shift M condition shifted ->
  source_bounded M a (succM M k) ->source_bounded M b (succM M k) ->source_bounded M guard (succM M k) ->
  sf_relation M SFImpl a b ab ->sf_relation M SFImpl shifted ab point ->sf_relation M SFAll point (zeroM M) qpoint ->
  sf_relation M SFImpl guard a ga ->sf_relation M SFImpl guard b gb ->
  sf_relation M SFAll ga (zeroM M) qa ->sf_relation M SFAll gb (zeroM M) qb ->
  sf_relation M SFImpl qa qb qmap ->sf_relation M SFImpl condition qmap cond ->sf_relation M SFImpl qpoint cond out ->
  source_full_prv M (zeroM M) (zeroM M) (zeroM M) out.
Proof.
  intros HC HS HA HB HG HAB HPoint HQPoint HGA HGB HQA HQB HMap HCond HOut.
  pose proof (source_shift_bound M condition shifted k HC HS) as HShifted.
  assert (HABound:source_bounded M ab (succM M k)).
  { exact (proj2 (source_bounded_accept_binary M SFImpl a b ab (succM M k)
      (or_intror (or_intror eq_refl)) HAB) (conj HA HB)). }
  assert (HPointBound:source_bounded M point (succM M k)).
  { exact (proj2 (source_bounded_accept_binary M SFImpl shifted ab point (succM M k)
      (or_intror (or_intror eq_refl)) HPoint) (conj HShifted HABound)). }
  assert (HGaBound:source_bounded M ga (succM M k)).
  { exact (proj2 (source_bounded_accept_binary M SFImpl guard a ga (succM M k)
      (or_intror (or_intror eq_refl)) HGA) (conj HG HA)). }
  assert (HGbBound:source_bounded M gb (succM M k)).
  { exact (proj2 (source_bounded_accept_binary M SFImpl guard b gb (succM M k)
      (or_intror (or_intror eq_refl)) HGB) (conj HG HB)). }
  pose proof (proj2 (source_bounded_accept_unary M SFAll point qpoint k (or_introl eq_refl) HQPoint) HPointBound) as BQP.
  pose proof (proj2 (source_bounded_accept_unary M SFAll ga qa k (or_introl eq_refl) HQA) HGaBound) as BQA.
  pose proof (proj2 (source_bounded_accept_unary M SFAll gb qb k (or_introl eq_refl) HQB) HGbBound) as BQB.
  assert (BMap:source_bounded M qmap k).
  { exact (proj2 (source_bounded_accept_binary M SFImpl qa qb qmap k
      (or_intror (or_intror eq_refl)) HMap) (conj BQA BQB)). }
  assert (BCond:source_bounded M cond k).
  { exact (proj2 (source_bounded_accept_binary M SFImpl condition qmap cond k
      (or_intror (or_intror eq_refl)) HCond) (conj HC BMap)). }
  assert (BOut:source_bounded M out k).
  { exact (proj2 (source_bounded_accept_binary M SFImpl qpoint cond out k
      (or_intror (or_intror eq_refl)) HOut) (conj BQP BCond)). }
  destruct (environment_cons_total M (zeroM M) (zeroM M) (zeroM M) qpoint) as (b1&c1&n1&H1).
  pose proof (proj2 (context_bounded_cons M _ _ _ qpoint b1 c1 n1 k H1)
    (conj BQP (context_bounded_empty M (zeroM M) (zeroM M) k))) as HC1.
  destruct (environment_cons_total M b1 c1 n1 condition) as (b2&c2&n2&H2).
  pose proof (proj2 (context_bounded_cons M b1 c1 n1 condition b2 c2 n2 k H2) (conj HC HC1)) as HC2.
  destruct (environment_cons_total M b2 c2 n2 qa) as (b3&c3&n3&H3).
  pose proof (proj2 (context_bounded_cons M b2 c2 n2 qa b3 c3 n3 k H3) (conj BQA HC2)) as HC3.
  assert (MQP:context_member M b3 c3 n3 qpoint).
  { apply (source_cons_tail_inclusion M b2 c2 n2 qa b3 c3 n3 H3).
    apply (source_cons_tail_inclusion M b1 c1 n1 condition b2 c2 n2 H2).
    apply (proj2 (context_member_cons M _ _ _ qpoint b1 c1 n1 qpoint H1)). now left. }
  assert (MQA:context_member M b3 c3 n3 qa).
  { apply (proj2 (context_member_cons M b2 c2 n2 qa b3 c3 n3 qa H3)). now left. }
  assert (PC:source_full_prv M b3 c3 n3 condition).
  { apply full_source_Ctx;[exists k;auto|].
    apply (source_cons_tail_inclusion M b2 c2 n2 qa b3 c3 n3 H3).
    apply (proj2 (context_member_cons M b1 c1 n1 condition b2 c2 n2 condition H2)). now left. }
  destruct (context_shift_total M b3 c3 n3) as (sb&sc&HShift).
  pose proof (context_shift_preserves_bound M b3 c3 n3 sb sc k HShift HC3) as HSC.
  pose proof (source_full_shifted_universal_hyp M b3 c3 n3 sb sc point qpoint (succM M k)
    (ex_intro _ k HC3) HShift MQP HPointBound HQPoint) as PPoint.
  pose proof (source_full_shifted_universal_hyp M b3 c3 n3 sb sc ga qa (succM M k)
    (ex_intro _ k HC3) HShift MQA HGaBound HQA) as PGa.
  pose proof (source_full_prv_renaming M b3 c3 n3 condition (zeroM M) (zeroM M) (zeroM M)
    (code_numeral M 1) sb sc shifted PC HShift HS) as PShifted.
  pose proof (source_full_modus_ponens M sb sc n3 shifted ab point HPoint PPoint PShifted) as PAB.
  destruct (environment_cons_total M sb sc n3 guard) as (ub&uc&un&HGuard).
  pose proof (proj2 (context_bounded_cons M sb sc n3 guard ub uc un (succM M k) HGuard) (conj HG HSC)) as HUC.
  pose proof (source_full_cons_weaken M sb sc n3 guard ub uc un (succM M k) ga HGuard HUC PGa) as PGaU.
  pose proof (source_full_cons_weaken M sb sc n3 guard ub uc un (succM M k) ab HGuard HUC PAB) as PABU.
  pose proof (source_full_cons_head M sb sc n3 guard ub uc un (succM M k) HGuard HG HUC) as PG.
  pose proof (source_full_modus_ponens M ub uc un guard a ga HGA PGaU PG) as PA.
  pose proof (source_full_modus_ponens M ub uc un a b ab HAB PABU PA) as PB.
  pose proof (full_source_II M sb sc n3 guard b gb ub uc un
    (ex_intro _ (succM M k) (conj HGbBound HSC)) PB HGuard HGB) as PGb.
  pose proof (full_source_AllI M b3 c3 n3 gb qb sb sc (ex_intro _ k (conj BQB HC3)) PGb HShift HQB) as PQB.
  pose proof (full_source_II M b2 c2 n2 qa qb qmap b3 c3 n3 (ex_intro _ k (conj BMap HC2)) PQB H3 HMap) as PMap.
  pose proof (full_source_II M b1 c1 n1 condition qmap cond b2 c2 n2 (ex_intro _ k (conj BCond HC1)) PMap H2 HCond) as PCond.
  exact (full_source_II M (zeroM M) (zeroM M) (zeroM M) qpoint cond out b1 c1 n1
    (ex_intro _ k (conj BOut (context_bounded_empty M (zeroM M) (zeroM M) k))) PCond H1 HOut).
Qed.

Print Assumptions source_conditional_universal_map.
