(** Literal paths are only recovered after a finite depth is known.
    The machine invariant itself remains the arithmetic dispatch-code graph. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
 PowerTwoSyntax PowerTwoRecurrence PowerTwoPositive TM230LiteralActions TM230BitArithmetic
 TM230DispatchWords TM230DispatchPathCode TM230DispatchCode Program230PathCode.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lists.List setoid_ring.Ring Lia.
Import ListNotations.
Unset Implicit Arguments.
Section Calibration.
Variable M:Model.
Local Notation Z:=(zeroM M).
Local Notation S:=(succM M).
Local Notation one:=(S Z).
Local Notation two:=(S one).
Local Notation N:=(code_numeral M).
Local Infix "+":=(addM M).
Local Infix "*":=(mulM M).
Add Ring machine230_dispatch_calibration_ring:(model_semiring M).
Theorem machine230_dispatch_low_bound P p:
 power2 M(N(length P))p ->coding_lt M(machine230_dispatch_bits M P Z)p.
Proof.
 revert p. induction P as[|b P IH];intros p HP.
 -rewrite(power2_zero_value M p HP). apply coding_lt_succ.
 -change(power2 M(S(N(length P)))p)in HP.
  destruct(power2_successor_inv M(N(length P))p HP)as[q[Hq Ep]].
  change(p=two*q)in Ep. destruct(IH q Hq)as[d Ed].
  cbn[machine230_dispatch_bits]. rewrite Ep,Ed.
  destruct b.
  +exists(two*d). change(two*S(machine230_dispatch_bits M P Z+d)=
    S(one+two*machine230_dispatch_bits M P Z+two*d)).
   rewrite(succ_as_add M(machine230_dispatch_bits M P Z+d)),
    (succ_as_add M(one+two*machine230_dispatch_bits M P Z+two*d)). rewrite(succ_as_add M one);ring.
  +exists(S(two*d)). change(two*S(machine230_dispatch_bits M P Z+d)=
    S(Z+two*machine230_dispatch_bits M P Z+S(two*d))).
   rewrite(succ_as_add M(machine230_dispatch_bits M P Z+d)),
    (succ_as_add M(Z+two*machine230_dispatch_bits M P Z+S(two*d))),
    (succ_as_add M(two*d)),(succ_as_add M one);ring.
Qed.
Lemma machine230_dispatch_quotient_bound h r q:
 coding_lt M(two*r+h)(two*q)->coding_lt M r q.
Proof.
 intro H. assert(HB:forall d,r=q+d->False).
 {intros d ->. destruct H as[k Hk].
  assert(EE:two*q=two*q+S(two*d+h+k)).
  {rewrite Hk at 1. rewrite(succ_as_add M(two*(q+d)+h+k)),
    (succ_as_add M(two*d+h+k));ring. }
  apply(zero_ne_succ M(two*d+h+k));apply(Arithmetic.add_cancel M Z(S(two*d+h+k))(two*q));
   rewrite Arithmetic.add_zero,(Arithmetic.add_comm M(S(two*d+h+k))(two*q));exact EE. }
 destruct(@Peano.trichotomy(carrier M)(raw_interpretation M)
  (fun ax H rho=>axioms M ax rho H)r q)as[Hr|[E|Hr]];[exact Hr|exfalso|exfalso].
 -apply(HB Z);rewrite E;ring.
 -destruct Hr as[d Hd]. apply(HB(S d)). change(r=S(q+d))in Hd.
  rewrite Hd,(succ_as_add M(q+d)),(succ_as_add M d);ring.
Qed.
Theorem machine230_dispatch_bits_decode n p low:
 power2 M(N n)p ->coding_lt M low p ->
 exists P,length P=n /\machine230_dispatch_bits M P Z=low.
Proof.
 revert p low. induction n as[|n IH];intros p low HP Hlow.
 -rewrite(power2_zero_value M p HP)in Hlow.
  apply coding_lt_succ_cases in Hlow. destruct Hlow as[Hfalse|E];
  [exfalso;exact(coding_not_lt_zero M low Hfalse)|]. exists[];split;[reflexivity|symmetry;exact E].
 -change(power2 M(S(N n))p)in HP.
  destruct(power2_successor_inv M(N n)p HP)as[q[Hq Ep]]. change(p=two*q)in Ep.
  destruct(machine230_pop_total M low)as[h[r[Hbit Eword]]].
  assert(Hr:coding_lt M r q).
  {apply(machine230_dispatch_quotient_bound h r q);rewrite <-Eword,<-Ep;exact Hlow. }
  destruct(IH q r Hq Hr)as[P[HL ER]].
  destruct Hbit as[Eh|Eh];[exists(false::P)|exists(true::P)];split;try(now cbn;rewrite HL);
  cbn[machine230_dispatch_bits machine230_bitM machine230_bit code_numeral];rewrite ER;rewrite Eword,Eh;ring.
Qed.
Theorem machine230_dispatch_code_calibration P gap constant file s:
 machine230_dispatch_view M P gap constant file s <->
 machine230_dispatch_code_view M(program230_path_value M P)(N(length P))(gap+N constant)file s.
Proof.
 unfold machine230_dispatch_view,machine230_dispatch_code_view. split.
 -intros[q[Hq Hs]]. destruct(power2_total M(N(length P)))as[p Hp].
  exists(machine230_dispatch_bits M P Z),p,q.
  split;[exact Hp|]. split;[now apply machine230_dispatch_low_bound|].
  split;[rewrite machine230_dispatch_path_code,(machine230_dispatch_bits_linear M P p one Hp);ring|].
  split;[exact Hq|]. rewrite(machine230_dispatch_bits_linear M P p(q*(one+two*file)))in Hs by exact Hp.
  replace(machine230_dispatch_bits M P Z+p*(q*(one+two*file)))with
   (machine230_dispatch_bits M P Z+(p*q)*(one+two*file))in Hs by ring. exact Hs.
 -intros[low[p[q[Hp[Hlow[Epc[Hq Hs]]]]]]]. exists q;split;[exact Hq|].
  assert(EL:low=machine230_dispatch_bits M P Z).
  {apply(Arithmetic.add_cancel M low(machine230_dispatch_bits M P Z)p).
   rewrite <-Epc,machine230_dispatch_path_code,(machine230_dispatch_bits_linear M P p one Hp);ring. }
  rewrite EL in Hs. rewrite(machine230_dispatch_bits_linear M P p(q*(one+two*file)))by exact Hp.
  replace(machine230_dispatch_bits M P Z+p*(q*(one+two*file)))with
   (machine230_dispatch_bits M P Z+(p*q)*(one+two*file))by ring. exact Hs.
Qed.
Theorem machine230_dispatch_code_decode n pc gap file s:
 machine230_dispatch_code_view M pc(N n)gap file s ->
 exists P,length P=n /\pc=program230_path_value M P /\
 machine230_dispatch_view M P gap 0 file s.
Proof.
 intros[low[p[q[Hp[Hlow[Epc[Hq Hs]]]]]]].
 destruct(machine230_dispatch_bits_decode n p low Hp Hlow)as[P[HL EL]].
 exists P;split;[exact HL|]. split.
 -rewrite Epc,<-EL,machine230_dispatch_path_code,(machine230_dispatch_bits_linear M P p one)by(now rewrite HL);ring.
 -apply machine230_dispatch_code_calibration. rewrite HL,coding_add_zero_r.
  assert(EPC:pc=program230_path_value M P).
  {rewrite Epc,<-EL,machine230_dispatch_path_code,(machine230_dispatch_bits_linear M P p one)by(now rewrite HL);ring. }
  rewrite <-EPC. exists low,p,q;auto.
Qed.
End Calibration.
Print Assumptions machine230_dispatch_low_bound.
Print Assumptions machine230_dispatch_bits_decode.
Print Assumptions machine230_dispatch_code_calibration.
Print Assumptions machine230_dispatch_code_decode.
