(** Paired actual carry and rollback paths, with no prefix-existence premise. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT TM230UnaryBlocks
 TM230BitArithmetic TM230LeftView TM230ExactPaths TM230CarryChainSyntax
 TM230CarryPrefixes TM230ViewRuns TM230CarryRollbackPoint TM230CarryRollbackInvariant.
Unset Implicit Arguments.
Section Paired.
Variable M:Model.
Local Notation O:=(zeroM M).
Local Notation S:=(succM M).
Local Notation one:=(S O).
Local Infix "+":=(addM M).
Lemma carry_rollback_word_prefix vb vc wb wc n:
 machine230_carry_chain M vb vc wb wc(S n)->machine230_carry_chain M vb vc wb wc n.
Proof. intros H i Hi;apply H;apply coding_lt_succ_cases;now left. Qed.
Lemma carry_rollback_left_prefix vb vc lb lc n:
 machine230_carry_prefix_chain M vb vc lb lc(S n)->machine230_carry_prefix_chain M vb vc lb lc n.
Proof. intros H i Hi;apply H;apply coding_lt_succ_cases;now left. Qed.
Theorem machine230_carry_rollback_uniform vb vc wb wc lb lc:forall count,
 machine230_carry_rollback_at M vb vc wb wc lb lc count.
Proof.
 apply(definable_induction M(machine230_carry_rollback_at M vb vc wb wc lb lc)
  (machine230_carry_rollback_definable M vb vc wb wc lb lc)).
 - intros a b x y HW HL HA HB HX HY.
   assert(Eb:b=a)by(eapply beta_unique;eassumption). subst b.
   assert(Ey:y=x)by(eapply beta_unique;eassumption). subst y.
   split;apply machine230_bounded_view_run_zero.
 - intros n IH a b x y HW HL HA HB HX HY.
   destruct(HW n(coding_lt_succ M n))as[v[xn[yn[HV[HXn[HYn Hblock]]]]]].
   destruct(HL n(coding_lt_succ M n))as[v'[an[bn[HV'[HAn[HBn Hprefix]]]]]].
   assert(Ev:v'=v)by(eapply beta_unique;eassumption). subst v'.
   assert(Eb:bn=b)by(eapply beta_unique;eassumption). subst bn.
   assert(Ey:yn=y)by(eapply beta_unique;eassumption). subst yn.
   destruct(IH a an x xn(carry_rollback_word_prefix vb vc wb wc n HW)
    (carry_rollback_left_prefix vb vc lb lc n HL)HA HAn HX HXn)as[HF HR].
   split.
   + replace(S n)with(n+one)by(symmetry;apply succ_as_add).
     eapply machine230_bounded_view_run_join;[exact HF|].
     exact(machine230_carry_prefix_forward M v an b xn y Hblock Hprefix).
   + replace(S n)with(one+n)by(now rewrite Arithmetic.add_succ,Arithmetic.add_zero).
     eapply machine230_bounded_view_run_join;[|exact HR].
     exact(machine230_carry_prefix_backward M v an b xn y Hblock Hprefix).
Qed.
Theorem machine230_carry_rollback_total vb vc wb wc count left first last:
 machine230_carry_chain M vb vc wb wc count ->beta M wb wc O first ->beta M wb wc count last ->
 exists lb lc finalleft,beta M lb lc O left /\beta M lb lc count finalleft /\
 machine230_carry_prefix_chain M vb vc lb lc count /\
 machine230_bounded_view_run M false 0 count left first finalleft last /\
 machine230_bounded_view_run M true 97 count last finalleft first left.
Proof.
 intros HW Hfirst Hlast.
 destruct(machine230_carry_prefix_total M vb vc left count)as[lb[lc[H0 HL]]].
 destruct(beta_total M lb lc count)as[finalleft Hfinal].
 pose proof(machine230_carry_rollback_uniform vb vc wb wc lb lc count left finalleft first last
  HW HL H0 Hfinal Hfirst Hlast)as HP.
 exists lb,lc,finalleft;auto.
Qed.
Theorem machine230_bounded_view_from reverse q count a x b y s:
 machine230_bounded_view_run M reverse q count a x b y ->machine230_oriented_view M reverse q a x s ->
 exists t time slack,machine230_oriented_view M reverse q b y t /\time=count+slack /\machine230_reaches_in M time s t.
Proof.
 intros[slack[u[t[HU[HT HP]]]]]HS.
 assert(E:u=s)by(eapply machine230_oriented_view_unique;eassumption). subst u.
 exists t,(count+slack),slack;auto.
Qed.
Theorem machine230_bounded_view_from_positive reverse q count a x b y s:
 machine230_bounded_view_run M reverse q count a x b y ->machine230_oriented_view M reverse q a x s ->
 coding_lt M O count ->exists t time,machine230_oriented_view M reverse q b y t /\
 coding_lt M O time /\machine230_reaches_in M time s t.
Proof.
 intros HP HS[c HC]. destruct(machine230_bounded_view_from reverse q count a x b y s HP HS)
  as[t[time[slack[HT[Htime Hpath]]]]].
 exists t,time. split;[exact HT|]. split;[|exact Hpath].
 rewrite coding_add_zero in HC. rewrite Htime,HC,Arithmetic.add_succ. apply coding_zero_lt_succ.
Qed.
End Paired.
Print Assumptions machine230_carry_rollback_uniform.
Print Assumptions machine230_carry_rollback_total.
Print Assumptions machine230_bounded_view_from_positive.
