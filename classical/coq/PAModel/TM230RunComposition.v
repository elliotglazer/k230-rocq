(** Concatenation of genuinely internally finite four-field literal-TM histories.
    Both lengths range over an arbitrary PA model. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension
 BetaPacking NumericalEnvironments CodeExpressions TM230BinaryStep TM230RunArithmetic TM230StandardRun TM230StandardPacking.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lia setoid_ring.Ring.
Unset Implicit Arguments.
Definition machine230_run_from M b c N s0 :=
 machine230_state_at M b c (zeroM M) s0 /\ forall i s t,coding_lt M i N -> machine230_state_at M b c i s ->
 machine230_state_at M b c (succM M i) t -> machine230_step M s t.
Definition machine230_path M b c N s0 s1 :=
 machine230_run_from M b c N s0 /\ machine230_state_at M b c N s1.
Section MachineRunConcatenation.
Variable M:Model.
Local Notation D := (carrier M).
Local Notation Z := (zeroM M).
Local Notation S := (succM M).
Local Infix "+" := (addM M).
Local Infix "*" := (mulM M).
Local Notation four := (code_numeral M 4).
Add Ring machine230_history_ring : (model_semiring M).

Lemma machine230_lt_add_cancel a i n:
 coding_lt M (a+i)(a+n)->coding_lt M i n.
Proof.
 intros[d H]. exists d. apply(Arithmetic.add_cancel M n(S(i+d))a).
 replace(n+a)with(a+n)by ring. rewrite H.
 rewrite(succ_as_add M((a+i)+d)),(succ_as_add M(i+d)). ring.
Qed.
Lemma machine230_state_index_add a i j:
 machine230_state_index M(a+i)j=four*a+machine230_state_index M i j.
Proof. unfold machine230_state_index. ring. Qed.
Lemma machine230_state_index_bound i n j:
 (j<4)%nat->coding_lt M i n->coding_lt M(machine230_state_index M i j)(four*n).
Proof.
 intros Hj[d ->]. exists(four*d+code_numeral M(3-j)). unfold machine230_state_index.
 rewrite(succ_as_add M(i+d)),(succ_as_add M((four*i+code_numeral M j)+(four*d+code_numeral M(3-j)))).
 destruct j as[|[|[|[|j]]]];try lia;
 cbn[code_numeral Nat.sub];
 repeat match goal with |-context[succM M(succM M ?x)]=>rewrite(succ_as_add M(succM M x))end;ring.
Qed.

Lemma machine230_state_at_transport b c d e offset n:
 (forall k v,coding_lt M k(four*n)->beta M b c k v->beta M d e(four*offset+k)v)->
 forall i s,coding_lt M i n->machine230_state_at M b c i s->machine230_state_at M d e(offset+i)s.
Proof.
 intros H i[q l h r]Hi(H0&H1&H2&H3).
 change(beta M d e(machine230_state_index M(offset+i)0)q /\ (beta M d e(machine230_state_index M(offset+i)1)l /\ (beta M d e(machine230_state_index M(offset+i)2)h /\ beta M d e(machine230_state_index M(offset+i)3)r))).
 refine(conj _ (conj _ (conj _ _))).
 all:rewrite machine230_state_index_add;apply H;
 [apply machine230_state_index_bound;[lia|exact Hi]|assumption].
Qed.
Lemma machine230_state_at_preservation_iff b c d e i j:
 (forall s,machine230_state_at M b c i s->machine230_state_at M d e j s)->
 forall s,machine230_state_at M b c i s<->machine230_state_at M d e j s.
Proof.
 intros H s. split;[apply H|]. intro HS.
 destruct(machine230_state_at_total M b c i)as[t HT].
 pose proof(machine230_state_at_unique M d e j s t HS(H t HT))as E. now subst s.
Qed.

Theorem machine230_run_from_join b c N d e K s0 middle:
 machine230_run_from M b c N s0->machine230_state_at M b c N middle->
 machine230_run_from M d e K middle->
 exists f g,machine230_run_from M f g(N+K)s0 /\
  (forall i s,coding_lt M i(S N)->(machine230_state_at M b c i s<->machine230_state_at M f g i s)) /\
  (forall j s,coding_lt M j(S K)->(machine230_state_at M d e j s<->machine230_state_at M f g(N+j)s)).
Proof.
 intros[Hstart Hstep]Hmiddle[Hstart2 Hstep2].
 destruct(beta_concatenate M b c(four*N)d e(four*(S K)))as[f[g[HL HR]]].
 assert(R:forall j s,coding_lt M j(S K)->machine230_state_at M d e j s->machine230_state_at M f g(N+j)s).
 { intros j s Hj HS. exact(machine230_state_at_transport d e f g N(S K)HR j s Hj HS). }
 assert(L0:forall i s,coding_lt M i N->machine230_state_at M b c i s->machine230_state_at M f g i s).
 { intros i s Hi HS.
   assert(H:forall k v,coding_lt M k(four*N)->beta M b c k v->beta M f g(four*Z+k)v).
   { intros k v HK HV. replace(four*Z+k)with k by ring. exact(HL k v HK HV). }
   pose proof(machine230_state_at_transport b c f g Z N H i s Hi HS)as P.
   now rewrite coding_add_zero in P. }
 assert(L:forall i s,coding_lt M i(S N)->machine230_state_at M b c i s->machine230_state_at M f g i s).
 { intros i s Hi HS. apply coding_lt_succ_cases in Hi. destruct Hi as[Hi | E].
   - exact(L0 i s Hi HS).
   - subst i. pose proof(machine230_state_at_unique M b c N s middle HS Hmiddle)as E. subst s.
     pose proof(R Z middle(coding_zero_lt_succ M K)Hstart2)as P.
     now rewrite coding_add_zero_r in P. }
 assert(LI:forall i s,coding_lt M i(S N)->(machine230_state_at M b c i s<->machine230_state_at M f g i s)).
 { intros i s Hi. apply machine230_state_at_preservation_iff. intros t HT. exact(L i t Hi HT). }
 assert(RI:forall j s,coding_lt M j(S K)->(machine230_state_at M d e j s<->machine230_state_at M f g(N+j)s)).
 { intros j s Hj. apply machine230_state_at_preservation_iff. intros t HT. exact(R j t Hj HT). }
 exists f,g. split;[|split;assumption]. split.
 - exact(L Z s0(coding_zero_lt_succ M N)Hstart).
 - intros i s t Hi HS HT. destruct(environment_lt_cases M i N)as[Hleft|Hright].
   + apply(Hstep i s t Hleft).
     * apply(LI i s);[apply coding_lt_succ_cases;now left|exact HS].
     * apply(LI(S i)t);[apply coding_lt_succ_cancel;exact Hleft|exact HT].
   + destruct(coding_difference M i N Hright)as[j ->].
     assert(Hj:coding_lt M j K)by(exact(machine230_lt_add_cancel N j K Hi)).
     apply(Hstep2 j s t Hj).
     * apply(RI j s);[apply coding_lt_succ_cases;now left|exact HS].
     * apply(RI(S j)t);[apply coding_lt_succ_cancel;exact Hj|].
       replace(N+S j)with(S(N+j))by(rewrite(succ_as_add M j),(succ_as_add M(N+j));ring). exact HT.
Qed.
End MachineRunConcatenation.
Print Assumptions machine230_run_from_join.
