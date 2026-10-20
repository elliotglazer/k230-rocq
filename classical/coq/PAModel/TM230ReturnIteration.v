(** Actual return across an internally finite ordinary register file. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT TM230UnaryBlocks
 TM230BitArithmetic TM230LeftView TM230ExactPaths TM230ReverseBlocks TM230CarryChainSyntax
 TM230ReturnPrefixes TM230ViewRuns TM230ReturnInvariant.
Unset Implicit Arguments.
Section ReturnIteration.
Variable M:Model.
Local Notation O:=(zeroM M).
Local Notation S:=(succM M).
Local Notation one:=(S O).
Local Infix "+":=(addM M).
Lemma return_word_prefix vb vc wb wc n:
 machine230_carry_chain M vb vc wb wc(S n)->machine230_carry_chain M vb vc wb wc n.
Proof. intros H i Hi;apply H;apply coding_lt_succ_cases;now left. Qed.
Lemma return_left_prefix vb vc lb lc n:
 machine230_return_prefix_chain M vb vc lb lc(S n)->machine230_return_prefix_chain M vb vc lb lc n.
Proof. intros H i Hi;apply H;apply coding_lt_succ_cases;now left. Qed.
Theorem machine230_return_prefix_point v left out word tail:
 machine230_unary_block M v tail word ->machine230_reverse_block M v left out ->
 machine230_bounded_view_run M true 40 one tail out word left.
Proof.
 intros HW HL. destruct(machine230_left_view_total M 40 tail out)as[s HS].
 destruct(machine230_reverse_block_return M 40 54 40 v left tail out s eq_refl eq_refl eq_refl HL HS)
  as[restored[t[HR[HT HP]]]].
 assert(E:restored=word)by(eapply machine230_unary_block_functional;eassumption). subst restored.
 exists(S v). replace(one+S v)with(S(S v))by(now rewrite Arithmetic.add_succ,Arithmetic.add_zero).
 exists s,t. auto.
Qed.
Theorem machine230_return_uniform vb vc wb wc lb lc:forall count,
 machine230_return_at M vb vc wb wc lb lc count.
Proof.
 apply(definable_induction M(machine230_return_at M vb vc wb wc lb lc)
  (machine230_return_definable M vb vc wb wc lb lc)).
 - intros a b x y HW HL HA HB HX HY.
   assert(Eb:b=a)by(eapply beta_unique;eassumption). subst b.
   assert(Ey:y=x)by(eapply beta_unique;eassumption). subst y.
   apply machine230_bounded_view_run_zero.
 - intros n IH a b x y HW HL HA HB HX HY.
   destruct(HW n(coding_lt_succ M n))as[v[xn[yn[HV[HXn[HYn Hblock]]]]]].
   destruct(HL n(coding_lt_succ M n))as[v'[an[bn[HV'[HAn[HBn Hprefix]]]]]].
   assert(Ev:v'=v)by(eapply beta_unique;eassumption). subst v'.
   assert(Eb:bn=b)by(eapply beta_unique;eassumption). subst bn.
   assert(Ey:yn=y)by(eapply beta_unique;eassumption). subst yn.
   pose proof(IH a an x xn(return_word_prefix vb vc wb wc n HW)
    (return_left_prefix vb vc lb lc n HL)HA HAn HX HXn)as HR.
   replace(S n)with(one+n)by(now rewrite Arithmetic.add_succ,Arithmetic.add_zero).
   eapply machine230_bounded_view_run_join;[|exact HR].
   exact(machine230_return_prefix_point v an b xn y Hblock Hprefix).
Qed.
Theorem machine230_return_total vb vc wb wc count left first last:
 machine230_carry_chain M vb vc wb wc count ->beta M wb wc O first ->beta M wb wc count last ->
 exists lb lc finalleft,beta M lb lc O left /\beta M lb lc count finalleft /\
 machine230_return_prefix_chain M vb vc lb lc count /\
 machine230_bounded_view_run M true 40 count last finalleft first left.
Proof.
 intros HW Hfirst Hlast.
 destruct(machine230_return_prefix_total M vb vc left count)as[lb[lc[H0 HL]]].
 destruct(beta_total M lb lc count)as[finalleft Hfinal].
 pose proof(machine230_return_uniform vb vc wb wc lb lc count left finalleft first last
  HW HL H0 Hfinal Hfirst Hlast)as HP.
 exists lb,lc,finalleft;auto.
Qed.
Theorem machine230_return_from vb vc wb wc lb lc count left finalleft first last s:
 machine230_carry_chain M vb vc wb wc count ->
 machine230_return_prefix_chain M vb vc lb lc count ->
 beta M lb lc O left ->beta M lb lc count finalleft ->
 beta M wb wc O first ->beta M wb wc count last ->
 machine230_left_view M 40 last finalleft s ->
 exists t time slack,machine230_left_view M 40 first left t /\
 time=count+slack /\machine230_reaches_in M time s t.
Proof.
 intros HW HL H0 Hfinal Hfirst Hlast HS.
 destruct(machine230_return_uniform vb vc wb wc lb lc count left finalleft first last
  HW HL H0 Hfinal Hfirst Hlast)as[slack[u[t[HU[HT HP]]]]].
 assert(E:u=s)by(eapply machine230_oriented_view_unique;eassumption). subst u.
 exists t,(count+slack),slack;auto.
Qed.
Theorem machine230_return_from_positive vb vc wb wc lb lc count left finalleft first last s:
 machine230_carry_chain M vb vc wb wc count ->
 machine230_return_prefix_chain M vb vc lb lc count ->
 beta M lb lc O left ->beta M lb lc count finalleft ->
 beta M wb wc O first ->beta M wb wc count last ->
 machine230_left_view M 40 last finalleft s ->coding_lt M O count ->
 exists t time,machine230_left_view M 40 first left t /\
 coding_lt M O time /\machine230_reaches_in M time s t.
Proof.
 intros HW HL H0 Hfinal Hfirst Hlast HS[c HC].
 destruct(machine230_return_from vb vc wb wc lb lc count left finalleft first last s
  HW HL H0 Hfinal Hfirst Hlast HS)as[t[time[slack[HT[Htime HP]]]]].
 exists t,time. split;[exact HT|]. split;[|exact HP].
 rewrite coding_add_zero in HC. rewrite Htime,HC,Arithmetic.add_succ. apply coding_zero_lt_succ.
Qed.
End ReturnIteration.
Print Assumptions machine230_return_uniform.
Print Assumptions machine230_return_total.
Print Assumptions machine230_return_from.
Print Assumptions machine230_return_from_positive.
