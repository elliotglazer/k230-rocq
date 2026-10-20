(** Concatenation of genuinely internally finite six-register histories.
    Both lengths range over an arbitrary PA model. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension
 BetaPacking NumericalEnvironments CodeExpressions RunSyntax.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lia setoid_ring.Ring.
Unset Implicit Arguments.
Section RunConcatenation.
Variable M:Model.
Local Notation D := (carrier M).
Local Notation Z := (zeroM M).
Local Notation S := (succM M).
Local Infix "+" := (addM M).
Local Infix "*" := (mulM M).
Local Notation six := (code_numeral M 6).
Add Ring run_history_ring : (model_semiring M).

Lemma run_lt_add_cancel a i n:
 coding_lt M (a+i)(a+n)->coding_lt M i n.
Proof.
 intros[d H]. exists d. apply(Arithmetic.add_cancel M n(S(i+d))a).
 replace(n+a)with(a+n)by ring. rewrite H.
 rewrite(succ_as_add M((a+i)+d)),(succ_as_add M(i+d)). ring.
Qed.
Lemma run_state_index_add a i j:
 state_index M(a+i)j=six*a+state_index M i j.
Proof. unfold state_index. ring. Qed.
Lemma run_state_index_bound i n j:
 (j<6)%nat->coding_lt M i n->coding_lt M(state_index M i j)(six*n).
Proof.
 intros Hj[d ->]. exists(six*d+code_numeral M(5-j)). unfold state_index.
 rewrite(succ_as_add M(i+d)),(succ_as_add M((six*i+code_numeral M j)+(six*d+code_numeral M(5-j)))).
 destruct j as[|[|[|[|[|[|j]]]]]];try lia;
 cbn[code_numeral Nat.sub];
 repeat match goal with |-context[succM M(succM M ?x)]=>rewrite(succ_as_add M(succM M x))end;ring.
Qed.

Lemma run_state_at_transport b c d e offset n:
 (forall k v,coding_lt M k(six*n)->beta M b c k v->beta M d e(six*offset+k)v)->
 forall i s,coding_lt M i n->state_at M b c i s->state_at M d e(offset+i)s.
Proof.
 intros H i[pl np tw ws dd hh]Hi(H0&H1&H2&H3&H4&H5).
 change(beta M d e(state_index M(offset+i)0)pl /\
 (beta M d e(state_index M(offset+i)1)np /\
 (beta M d e(state_index M(offset+i)2)tw /\
 (beta M d e(state_index M(offset+i)3)ws /\
 (beta M d e(state_index M(offset+i)4)dd /\
 beta M d e(state_index M(offset+i)5)hh))))).
 refine(conj _ (conj _ (conj _ (conj _ (conj _ _))))).
 all:rewrite run_state_index_add;apply H;
 [apply run_state_index_bound;[lia|exact Hi]|assumption].
Qed.
Lemma run_state_at_preservation_iff b c d e i j:
 (forall s,state_at M b c i s->state_at M d e j s)->
 forall s,state_at M b c i s<->state_at M d e j s.
Proof.
 intros H s. split;[apply H|]. intro HS.
 destruct(state_at_total M b c i)as[t HT].
 pose proof(state_at_functional M d e j s t HS(H t HT))as E. now subst s.
Qed.

Theorem numerical_run_from_join b c N d e K s0 middle:
 numerical_run_from M b c N s0->state_at M b c N middle->
 numerical_run_from M d e K middle->
 exists f g,numerical_run_from M f g(N+K)s0 /\
  (forall i s,coding_lt M i(S N)->(state_at M b c i s<->state_at M f g i s)) /\
  (forall j s,coding_lt M j(S K)->(state_at M d e j s<->state_at M f g(N+j)s)).
Proof.
 intros[Hstart Hstep]Hmiddle[Hstart2 Hstep2].
 destruct(beta_concatenate M b c(six*N)d e(six*(S K)))as[f[g[HL HR]]].
 assert(R:forall j s,coding_lt M j(S K)->state_at M d e j s->state_at M f g(N+j)s).
 { intros j s Hj HS. exact(run_state_at_transport d e f g N(S K)HR j s Hj HS). }
 assert(L0:forall i s,coding_lt M i N->state_at M b c i s->state_at M f g i s).
 { intros i s Hi HS.
   assert(H:forall k v,coding_lt M k(six*N)->beta M b c k v->beta M f g(six*Z+k)v).
   { intros k v HK HV. replace(six*Z+k)with k by ring. exact(HL k v HK HV). }
   pose proof(run_state_at_transport b c f g Z N H i s Hi HS)as P.
   now rewrite coding_add_zero in P. }
 assert(L:forall i s,coding_lt M i(S N)->state_at M b c i s->state_at M f g i s).
 { intros i s Hi HS. apply coding_lt_succ_cases in Hi. destruct Hi as[Hi | E].
   - exact(L0 i s Hi HS).
   - subst i. pose proof(state_at_functional M b c N s middle HS Hmiddle)as E. subst s.
     pose proof(R Z middle(coding_zero_lt_succ M K)Hstart2)as P.
     now rewrite coding_add_zero_r in P. }
 assert(LI:forall i s,coding_lt M i(S N)->(state_at M b c i s<->state_at M f g i s)).
 { intros i s Hi. apply run_state_at_preservation_iff. intros t HT. exact(L i t Hi HT). }
 assert(RI:forall j s,coding_lt M j(S K)->(state_at M d e j s<->state_at M f g(N+j)s)).
 { intros j s Hj. apply run_state_at_preservation_iff. intros t HT. exact(R j t Hj HT). }
 exists f,g. split;[|split;assumption]. split.
 - exact(L Z s0(coding_zero_lt_succ M N)Hstart).
 - intros i s t Hi HS HT. destruct(environment_lt_cases M i N)as[Hleft|Hright].
   + apply(Hstep i s t Hleft).
     * apply(LI i s);[apply coding_lt_succ_cases;now left|exact HS].
     * apply(LI(S i)t);[apply coding_lt_succ_cancel;exact Hleft|exact HT].
   + destruct(coding_difference M i N Hright)as[j ->].
     assert(Hj:coding_lt M j K)by(exact(run_lt_add_cancel N j K Hi)).
     apply(Hstep2 j s t Hj).
     * apply(RI j s);[apply coding_lt_succ_cases;now left|exact HS].
     * apply(RI(S j)t);[apply coding_lt_succ_cancel;exact Hj|].
       replace(N+S j)with(S(N+j))by(rewrite(succ_as_add M j),(succ_as_add M(N+j));ring). exact HT.
Qed.
End RunConcatenation.
Print Assumptions numerical_run_from_join.
