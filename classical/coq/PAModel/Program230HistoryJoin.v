(** Genuine concatenation for arbitrary internal counterprogram history lengths. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension
 BetaPacking NumericalEnvironments CodeExpressions Program230Configurations Program230Histories.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lia setoid_ring.Ring.
Unset Implicit Arguments.
Section ProgramConcatenation.
Variable M:Model.
Variable step:form.
Local Notation D := (carrier M).
Local Notation Z := (zeroM M).
Local Notation S := (succM M).
Local Infix "+" := (addM M).
Local Infix "*" := (mulM M).
Local Notation ten := (code_numeral M 10).
Add Ring program_history_ring : (model_semiring M).

Lemma program230_lt_add_cancel a i n:
 coding_lt M (a+i)(a+n)->coding_lt M i n.
Proof.
 intros[d H]. exists d. apply(Arithmetic.add_cancel M n(S(i+d))a).
 replace(n+a)with(a+n)by ring. rewrite H.
 rewrite(succ_as_add M((a+i)+d)),(succ_as_add M(i+d)). ring.
Qed.
Lemma program230_field_index_add a i j:
 program230_field_index M(a+i)j=ten*a+program230_field_index M i j.
Proof. unfold program230_field_index. ring. Qed.
Lemma program230_field_index_bound i n j:
 (j<10)%nat->coding_lt M i n->coding_lt M(program230_field_index M i j)(ten*n).
Proof.
 intros Hj[d ->]. exists(ten*d+code_numeral M(9-j)). unfold program230_field_index.
 rewrite(succ_as_add M(i+d)),(succ_as_add M((ten*i+code_numeral M j)+(ten*d+code_numeral M(9-j)))).
 destruct j as[|[|[|[|[|[|[|[|[|[|j]]]]]]]]]];try lia;
 cbn[code_numeral Nat.sub];
 repeat match goal with |-context[succM M(succM M ?x)]=>rewrite(succ_as_add M(succM M x))end;ring.
Qed.

Lemma program230_state_at_transport b c d e offset n:
 (forall k v,coding_lt M k(ten*n)->beta M b c k v->beta M d e(ten*offset+k)v)->
 forall i s,coding_lt M i n->program230_state_at M b c i s->program230_state_at M d e(offset+i)s.
Proof.
 intros H i st Hi HS j Hj. rewrite program230_field_index_add.
 apply H;[apply program230_field_index_bound;assumption|exact(HS j Hj)].
Qed.
Lemma program230_state_at_preservation_iff b c d e i j:
 (forall s,program230_state_at M b c i s->program230_state_at M d e j s)->
 forall s,program230_state_at M b c i s<->program230_state_at M d e j s.
Proof.
 intros H s. split;[apply H|]. intro HS.
 destruct(program230_state_at_total M b c i)as[t HT].
 pose proof(program230_state_at_functional M d e j s t HS(H t HT))as E. now subst s.
Qed.

Theorem program230_history_join b c N d e K s0 middle:
 program230_history M step b c N s0->program230_state_at M b c N middle->
 program230_history M step d e K middle->
 exists f g,program230_history M step f g(N+K)s0 /\
  (forall i s,coding_lt M i(S N)->(program230_state_at M b c i s<->program230_state_at M f g i s)) /\
  (forall j s,coding_lt M j(S K)->(program230_state_at M d e j s<->program230_state_at M f g(N+j)s)).
Proof.
 intros[Hstart Hstep]Hmiddle[Hstart2 Hstep2].
 destruct(beta_concatenate M b c(ten*N)d e(ten*(S K)))as[f[g[HL HR]]].
 assert(R:forall j s,coding_lt M j(S K)->program230_state_at M d e j s->program230_state_at M f g(N+j)s).
 { intros j s Hj HS. exact(program230_state_at_transport d e f g N(S K)HR j s Hj HS). }
 assert(L0:forall i s,coding_lt M i N->program230_state_at M b c i s->program230_state_at M f g i s).
 { intros i s Hi HS.
   assert(H:forall k v,coding_lt M k(ten*N)->beta M b c k v->beta M f g(ten*Z+k)v).
   { intros k v HK HV. replace(ten*Z+k)with k by ring. exact(HL k v HK HV). }
   pose proof(program230_state_at_transport b c f g Z N H i s Hi HS)as P.
   now rewrite coding_add_zero in P. }
 assert(L:forall i s,coding_lt M i(S N)->program230_state_at M b c i s->program230_state_at M f g i s).
 { intros i s Hi HS. apply coding_lt_succ_cases in Hi. destruct Hi as[Hi | E].
   - exact(L0 i s Hi HS).
   - subst i. pose proof(program230_state_at_functional M b c N s middle HS Hmiddle)as E. subst s.
     pose proof(R Z middle(coding_zero_lt_succ M K)Hstart2)as P.
     now rewrite coding_add_zero_r in P. }
 assert(LI:forall i s,coding_lt M i(S N)->(program230_state_at M b c i s<->program230_state_at M f g i s)).
 { intros i s Hi. apply program230_state_at_preservation_iff. intros t HT. exact(L i t Hi HT). }
 assert(RI:forall j s,coding_lt M j(S K)->(program230_state_at M d e j s<->program230_state_at M f g(N+j)s)).
 { intros j s Hj. apply program230_state_at_preservation_iff. intros t HT. exact(R j t Hj HT). }
 exists f,g. split;[|split;assumption]. split.
 - exact(L Z s0(coding_zero_lt_succ M N)Hstart).
 - intros i s t Hi HS HT. destruct(environment_lt_cases M i N)as[Hleft|Hright].
   + apply(Hstep i s t Hleft).
     * apply(LI i s);[apply coding_lt_succ_cases;now left|exact HS].
     * apply(LI(S i)t);[apply coding_lt_succ_cancel;exact Hleft|exact HT].
   + destruct(coding_difference M i N Hright)as[j ->].
     assert(Hj:coding_lt M j K)by(exact(program230_lt_add_cancel N j K Hi)).
     apply(Hstep2 j s t Hj).
     * apply(RI j s);[apply coding_lt_succ_cases;now left|exact HS].
     * apply(RI(S j)t);[apply coding_lt_succ_cancel;exact Hj|].
       replace(N+S j)with(S(N+j))by(rewrite(succ_as_add M j),(succ_as_add M(N+j));ring). exact HT.
Qed.
End ProgramConcatenation.
Print Assumptions program230_history_join.
