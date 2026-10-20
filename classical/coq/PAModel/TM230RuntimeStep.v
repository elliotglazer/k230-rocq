(** Proof-producing interpretation of the exact finite symbolic runtime step.
    The two explicit Box premises are discharged by the separate concrete
    register-file adapter; no such premise is counted as full simulation. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions TM230LiteralActions
 TM230BinaryStep TM230BitArithmetic TM230LeftView TM230Paths TM230ExactPaths TM230RegisterPrefix
 TM230SymbolicCells TM230MacroProgress TM230RuntimeWords TM230RuntimeActions TM230RuntimePeel.
From K230 Require Runtime230Core TM230.
From BusyCoq Require TM.
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith setoid_ring.Ring.
Import ListNotations.
Unset Implicit Arguments.
Definition machine230_runtime_oracle_paths M(Box:Runtime230.boxst->carrier M->Prop)br:=
 forall q x q' x' extra left word s,
 Runtime230.oracle q br x=Some(q',x',extra)->Box x word->machine230_right_view M q left word s ->
 exists output t,Box x' output /\machine230_left_view M q' output
  (if extra then addM M(code_numeral M 1)(mulM M(code_numeral M 2)left)else left)t /\machine230_reaches M s t.
Definition machine230_runtime_step_ok M gap Box conf moved s:=exists t,
 machine230_runtime_view M gap Box conf t /\machine230_reaches M s t /\
 (moved=true->machine230_progresses M s t).
Lemma machine230_runtime_ok_same M gap Box conf s:
 machine230_runtime_view M gap Box conf s->machine230_runtime_step_ok M gap Box conf false s.
Proof. intro H;exists s;split;[exact H|]. split;[apply machine230_reaches_refl|discriminate]. Qed.
Lemma machine230_runtime_ok_reaches M gap Box conf s t:
 machine230_runtime_view M gap Box conf t->machine230_reaches M s t->
 machine230_runtime_step_ok M gap Box conf false s.
Proof. intros HV HR;exists t;split;[exact HV|]. split;[exact HR|discriminate]. Qed.
Lemma machine230_runtime_ok_one M gap Box conf s t:
 machine230_runtime_view M gap Box conf t->machine230_step M s t->
 machine230_runtime_step_ok M gap Box conf true s.
Proof.
 intros HV HS. destruct(machine230_reaches_in_one M s t HS)as[b[c HP]].
 exists t;split;[exact HV|]. split;[exists b,c,(succM M(zeroM M));exact HP|].
 intros _. exists b,c,(succM M(zeroM M));split;[apply coding_zero_lt_succ|exact HP].
Qed.
Section RuntimeStep.
Variable M:Model.
Variable gap:carrier M.
Variable Box:Runtime230.boxst->carrier M->Prop.
Variable br:Runtime230.branch.
Hypothesis Hhead:forall x word,Box x word->exists tail,word=mulM M(code_numeral M 2)tail.
Hypothesis Horacle:machine230_runtime_oracle_paths M Box br.
Local Notation Z:=(zeroM M).
Local Notation two:=(succM M(succM M Z)).
Local Infix "+":=(addM M).
Local Infix "*":=(mulM M).
Add Ring machine230_runtime_step_ring:(model_semiring M).
Theorem machine230_runtime_sstep_sound conf conf' moved s:
 Runtime230.sstep br conf=Some(conf',moved)->machine230_runtime_view M gap Box conf s->
 machine230_runtime_step_ok M gap Box conf' moved s.
Proof.
 intros HE HV. destruct conf as[[[q onleft]ls]rs]. destruct onleft;cbn[Runtime230.sstep]in HE.
 -destruct ls as[|[b|b a c|x]ls].
  +injection HE as <- <-. apply machine230_runtime_ok_same.
   exact(machine230_runtime_reorient_blank M gap Box q rs s HV).
  +injection HE as <- <-. apply machine230_runtime_ok_same.
   exact(machine230_runtime_reorient M gap Box q b ls rs s HV).
  +assert(P:forall dst flag,Runtime230.peel_left q b a c ls rs=Some(dst,flag)->
    machine230_runtime_step_ok M gap Box dst flag s).
   {intros dst flag HP. destruct(machine230_runtime_peel_left M gap Box q b a c ls rs dst flag s HP HV)as[-> HD].
    now apply machine230_runtime_ok_same. }
   destruct(Public230.tmn q b)as[[[w dir]q2]|]eqn:HT;[destruct dir|];try(now apply P).
   destruct(Nat.eqb q2 q)eqn:EQ;[|now apply P].
   apply Nat.eqb_eq in EQ;subst q2. injection HE as <- <-.
   destruct(machine230_runtime_scan_left M gap Box q b w a c ls rs s HT HV)as[t[HD HP]].
   exact(machine230_runtime_ok_reaches M gap Box _ s t HD HP).
  +discriminate.
 -destruct rs as[|[b|b a c|x]rs];[discriminate| | |].
  +destruct(Public230.tmn q b)as[[[w dir]q2]|]eqn:HT;[destruct dir|discriminate];injection HE as <- <-.
   *destruct(machine230_runtime_cell_left M gap Box q b w q2 ls rs s HT HV)as[t[HD HP]].
    exact(machine230_runtime_ok_one M gap Box _ s t HD HP).
   *destruct(machine230_runtime_cell_right M gap Box q b w q2 ls rs s HT HV)as[t[HD HP]].
    exact(machine230_runtime_ok_one M gap Box _ s t HD HP).
  +assert(P:forall dst flag,Runtime230.peel_right q b a c ls rs=Some(dst,flag)->
    machine230_runtime_step_ok M gap Box dst flag s).
   {intros dst flag HP. destruct(machine230_runtime_peel_right M gap Box q b a c ls rs dst flag s HP HV)as[-> HD].
    now apply machine230_runtime_ok_same. }
   destruct(Public230.tmn q b)as[[[w dir]q2]|]eqn:HT;[destruct dir|];try(now apply P).
   destruct(Nat.eqb q2 q)eqn:EQ;[|now apply P].
   apply Nat.eqb_eq in EQ;subst q2. injection HE as <- <-.
   destruct(machine230_runtime_scan_right M gap Box q b w a c ls rs s HT HV)as[t[HD HP]].
   exact(machine230_runtime_ok_reaches M gap Box _ s t HD HP).
  +destruct rs as[|r rs];[|discriminate].
   destruct(Runtime230.oracle q br x)as[[[q2 x2]extra]|]eqn:HO.
   *injection HE as <- <-. destruct HV as[l[r[HL[[Hnil HX]HS]]]].
    destruct(Horacle q x q2 x2 extra l r s HO HX HS)as[output[t[HX2[HT HP]]]].
    apply(machine230_runtime_ok_reaches M gap Box _ s t);[|exact HP].
    destruct extra.
    --exists(addM M(code_numeral M 1)(mulM M(code_numeral M 2)l)),output. split.
      ++exists l;split;[exact HL|]. apply machine230_cell_value;reflexivity.
      ++split;[split;[reflexivity|exact HX2]|exact HT].
    --exists l,output;split;[exact HL|]. split;[split;[reflexivity|exact HX2]|exact HT].
   *destruct(Public230.tmn q false)as[[[w dir]q2]|]eqn:HT;[destruct w,dir|];try discriminate.
    injection HE as <- <-. destruct HV as[l[r[HL[[Hnil HX]HS]]]].
    destruct(Hhead x r HX)as[tail E]. change(r=two*tail)in E.
    destruct(machine230_left_view_total M q2 r l)as[t HTV].
    apply(machine230_runtime_ok_one M gap Box _ s t).
    --exists l,r;split;[exact HL|]. split;[split;[reflexivity|exact HX]|exact HTV].
    --apply(machine230_right_to_left_step M q false false q2 l tail s t HT).
      ++change(machine230_right_view M q l(Z+two*tail)s).
        replace(Z+two*tail)with r;[exact HS|rewrite E;ring].
      ++change(machine230_left_view M q2(Z+two*tail)l t).
        replace(Z+two*tail)with r;[exact HTV|rewrite E;ring].
Qed.
End RuntimeStep.
Print Assumptions machine230_runtime_sstep_sound.


