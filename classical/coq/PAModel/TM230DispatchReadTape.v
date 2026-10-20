(** Reading unused zero PC bits changes only the position of the gap.
    The proof preserves the exact tape word in an arbitrary PA model. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
 PowerTwoSyntax PowerTwoRecurrence PowerTwoLaws TM230BitArithmetic TM230LiteralActions
 TM230DispatchWords TM230DispatchPathCode.
From Stdlib Require Import Lists.List setoid_ring.Ring.
Import ListNotations.
Unset Implicit Arguments.
Section ReadTape.
Variable M:Model.
Local Notation Z:=(zeroM M).
Local Notation S:=(succM M).
Local Notation one:=(S Z).
Local Notation two:=(S one).
Local Notation N:=(code_numeral M).
Local Infix "+":=(addM M).
Local Infix "*":=(mulM M).
Add Ring dispatch_read_ring:(model_semiring M).
Lemma machine230_false_bits_zero P:
 Forall(eq false)P ->machine230_dispatch_bits M P Z=Z.
Proof.
 intro H;induction H as[|b P Hb HP IH];[reflexivity|].
 rewrite <-Hb. cbn[machine230_dispatch_bits machine230_bitM machine230_bit code_numeral].
 rewrite IH;ring.
Qed.
Lemma machine230_false_firstn P n:
 Forall(eq false)P->Forall(eq false)(firstn n P).
Proof. revert P;induction n;intros P H;[constructor|]. destruct H;cbn;constructor;auto. Qed.
Lemma machine230_false_repeat n:Forall(eq false)(repeat false n).
Proof. induction n;cbn;constructor;auto. Qed.
Theorem machine230_dispatch_read_low P n:
 Forall(eq false)(skipn n P)->
 machine230_dispatch_bits M P Z=
 machine230_dispatch_bits M(firstn n(P++repeat false n))Z.
Proof.
 intro Htail. pose proof(machine230_dispatch_bits_append M(firstn n P)(skipn n P)Z)as E.
 rewrite firstn_skipn,(machine230_false_bits_zero(skipn n P)Htail)in E.
 rewrite E,firstn_app,machine230_dispatch_bits_append.
 rewrite(machine230_false_bits_zero(firstn(n-length P)(repeat false n))).
 -reflexivity.
 -apply machine230_false_firstn;apply machine230_false_repeat.
Qed.
Theorem machine230_dispatch_read_view P Q n gap gap' file s:
 Q=firstn n(P++repeat false n)->Forall(eq false)(skipn n P)->
 N(length P)+gap=N(length Q)+gap' ->
 machine230_dispatch_view M P gap 0 file s ->
 machine230_dispatch_view M Q gap' 0 file s.
Proof.
 intros EQ Hclean Etotal [q[Hq Hs]].
 rewrite coding_add_zero_r in Hq.
 destruct(power2_total M gap')as[q' Hq'].
 destruct(power2_total M(N(length P)))as[p Hp].
 destruct(power2_total M(N(length Q)))as[p' Hp'].
 pose proof(power2_add M(N(length P))p Hp gap q Hq)as Htotal.
 pose proof(power2_add M(N(length Q))p' Hp' gap' q' Hq')as Htotal'.
 rewrite Etotal in Htotal.
 pose proof(power2_functional M(N(length Q)+gap')(p*q)(p'*q')Htotal Htotal')as Epower.
 assert(Elow:machine230_dispatch_bits M P Z=machine230_dispatch_bits M Q Z).
 {rewrite EQ;apply machine230_dispatch_read_low;exact Hclean. }
 exists q';split;[now rewrite coding_add_zero_r|].
 rewrite(machine230_dispatch_bits_linear M P p(q*(one+two*file))Hp)in Hs.
 rewrite(machine230_dispatch_bits_linear M Q p'(q'*(one+two*file))Hp').
 replace(machine230_dispatch_bits M Q Z+p'*(q'*(one+two*file)))with
  (machine230_dispatch_bits M P Z+(p*q)*(one+two*file)).
 -replace(machine230_dispatch_bits M P Z+(p*q)*(one+two*file))with
  (machine230_dispatch_bits M P Z+p*(q*(one+two*file)))by ring;exact Hs.
 -rewrite Elow,Epower;ring.
Qed.
End ReadTape.
Print Assumptions machine230_dispatch_read_low.
Print Assumptions machine230_dispatch_read_view.
