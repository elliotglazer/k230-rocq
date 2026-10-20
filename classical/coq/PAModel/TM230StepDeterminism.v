(** Determinism of the literal arithmetic machine in arbitrary PA models. *)
From PAModel Require Import Model Arithmetic CodeExpressions TM230LiteralActions
 TM230TransitionArithmetic TM230BinaryStep TM230BitArithmetic TM230MacroProgress.
From BusyCoq Require TM.
Unset Implicit Arguments.
Theorem machine230_transition_functional M q read w d next w' d' next':
 machine230_transition M q read w d next ->machine230_transition M q read w' d' next' ->
 w=w' /\d=d' /\next=next'.
Proof.
 intros[a[Ha HR]][a'[Ha' HR']].
 destruct a as[[[[qa ba]wa]da]na],a' as[[[[qb bb]wb]db]nb].
 unfold machine230_action_relation in HR,HR';cbn in HR,HR'.
 destruct HR as[Hq[Hb[Hw[Hd Hn]]]],HR' as[Hq'[Hb'[Hw'[Hd' Hn']]]].
 assert(Eq:qa=qb)by(apply(machine230_numeral_injective M);congruence). subst qb.
 assert(Eb:ba=bb).
 {apply machine230_bit_injective. apply(machine230_numeral_injective M);congruence. } subst bb.
 apply machine230_action_exact in Ha,Ha'. rewrite Ha in Ha'.
 injection Ha' as Ew Ed En. subst wb db nb. repeat split;congruence.
Qed.
Theorem machine230_step_functional M s t u:
 machine230_step M s t ->machine230_step M s u ->t=u.
Proof.
 destruct s as[sq sl sh sr],t as[tq tl th tr],u as[uq ul uh ur].
 unfold machine230_step;cbn[machine230_state machine230_left machine230_head machine230_right].
 intros[w[d[HT[HB HM]]]][w'[d'[HT'[HB' HM']]]].
 destruct(machine230_transition_functional M sq sh w d tq w' d' uq HT HT')as[Ew[Ed Eq]].
 subst w' d' uq.
 destruct HM as[[HL[ER EL]]|[HR[EL ER]]],HM' as[[HL'[ER' EL']]|[HR'[EL' ER']]].
 -destruct(machine230_pop_unique M th tl uh ul HB HB' (eq_trans(eq_sym EL)EL'))as[Eh El].
  assert(Er:tr=ur)by congruence. now subst.
 -exfalso. apply(zero_ne_succ M(zeroM M)). change(zeroM M=code_numeral M 1). congruence.
 -exfalso. apply(zero_ne_succ M(zeroM M)). change(zeroM M=code_numeral M 1). congruence.
 -destruct(machine230_pop_unique M th tr uh ur HB HB' (eq_trans(eq_sym ER)ER'))as[Eh Er].
  assert(El:tl=ul)by congruence. now subst.
Qed.
Print Assumptions machine230_transition_functional.
Print Assumptions machine230_step_functional.
