(** Auxiliary runtime operations for finite command templates.  Their graphs
    are the already proved arithmetic graphs.  No internal iteration is
    performed using these externally selected functions. *)
From PAModel Require Import Model Arithmetic Pairing CodeExpressions SearchStep
  NumericalCommands NumericalReachability NumericalSearchDrain.
From Stdlib Require Import Logic.ClassicalChoice Bool.Bool Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Theorem numerical_runtime_operations M :
  exists P : carrier M -> carrier M -> carrier M,
  exists U : carrier M -> carrier M * carrier M,
  exists E : carrier M -> carrier M -> bool,
    (forall a b,pair_graph M a b(P a b)) /\
    (forall z,pair_graph M(fst(U z))(snd(U z))z) /\
    (forall a b,E a b=true <->a=b).
Proof.
  assert(Hp:forall ab:carrier M*carrier M,exists z,pair_graph M(fst ab)(snd ab)z).
  { intros[a b]. apply pair_total. }
  destruct(choice _ Hp)as[P HP].
  assert(Hu:forall z:carrier M,exists ab:carrier M*carrier M,pair_graph M(fst ab)(snd ab)z).
  { intro z. destruct(pair_surjective M z)as[a[b H]]. exists(a,b);exact H. }
  destruct(choice _ Hu)as[U HU].
  assert(He:forall ab:carrier M*carrier M,exists e:bool,e=true <->fst ab=snd ab).
  { intros[a b]. destruct(Classical_Prop.classic(a=b))as[H|H].
    - exists true. tauto.
    - exists false. split;[discriminate|contradiction]. }
  destruct(choice _ He)as[E HE].
  exists(fun a b=>P(a,b)),U,(fun a b=>E(a,b)). split.
  - intros a b. exact(HP(a,b)).
  - split;[exact HU|]. intros a b. exact(HE(a,b)).
Qed.

Section Runtime.
Variable M:Model.
Local Notation D := (carrier M).
Local Notation O := (zeroM M).
Local Notation N := (code_numeral M).
Variable P:D->D->D.
Variable U:D->D*D.
Variable E:D->D->bool.
Hypothesis HP:forall a b,pair_graph M a b(P a b).
Hypothesis HU:forall z,pair_graph M(fst(U z))(snd(U z))z.
Hypothesis HE:forall a b,E a b=true <->a=b.

Fixpoint runtime_value(env:nat->D)(e:code_expr):D:=
 match e with
 |CEconst n=>N n|CEvar i=>env i
 |CEadd a b=>addM M(runtime_value env a)(runtime_value env b)
 |CEmul a b=>mulM M(runtime_value env a)(runtime_value env b)
 |CEpair a b=>P(runtime_value env a)(runtime_value env b)
 end.
Lemma runtime_value_graph env e:code_relation M env e(runtime_value env e).
Proof.
 induction e;cbn [runtime_value code_relation];try reflexivity;
 eexists;eexists;repeat split;eauto.
Qed.
Lemma runtime_unpair a b:U(P a b)=(a,b).
Proof.
 destruct(U(P a b))as[x y]eqn:H.
 pose proof(HU(P a b))as Hxy;rewrite H in Hxy;cbn in Hxy.
 destruct(pair_injective M(P a b)x y a b Hxy(HP a b))as[-> ->]. reflexivity.
Qed.
Lemma runtime_eq_false a b:E a b=false <->a<>b.
Proof.
 split.
 - intros Hf Hab;subst b. pose proof(proj2(HE a a)eq_refl). congruence.
 - intro H;destruct(E a b)eqn:He;[exfalso;apply H;now apply HE|reflexivity].
Qed.

Definition runtime_wim a b:=runtime_value(search_values M[a;b])(E_wim(CEvar 0)(CEvar 1)).
Definition runtime_bundle a b c:=runtime_value(search_values M[a;b;c])(E_bundle(CEvar 0)(CEvar 1)(CEvar 2)).
Definition runtime_stack a h b c u t w:=runtime_value(search_values M[a;h;b;c;u;t;w])
 (E_ax_stack(CEvar 0)(CEvar 1)(CEvar 2)(CEvar 3)(CEvar 4)(CEvar 5)(CEvar 6)).
Definition runtime_gate a b c:=if E c a || E c b then O else runtime_bundle a b c.
Lemma runtime_gate_spec a b c:
 ((c=a \/c=b)/\runtime_gate a b c=O)\/
 (c<>a/\c<>b/\search_bundle M a b c(runtime_gate a b c)).
Proof.
 unfold runtime_gate. destruct(E c a)eqn:Ha, (E c b)eqn:Hb;cbn -[runtime_bundle].
 - left. split;[left;now apply HE|reflexivity].
 - left. split;[left;now apply HE|reflexivity].
 - left. split;[right;now apply HE|reflexivity].
 - right. split;[now apply runtime_eq_false|]. split;[now apply runtime_eq_false|].
   exact(runtime_value_graph(search_values M[a;b;c])(E_bundle(CEvar 0)(CEvar 1)(CEvar 2))).
Qed.

Inductive runtime_command:Type:=
| Rcmp(x:D)|Rdrop|Rnip|Rax(c x y u:D).
Definition runtime_registers:Type:=(D*D*D*D)%type.
Definition runtime_state p np(q:runtime_registers):search_state D:=
 let '(t,w,d,h):=q in command_state M p np t w d h.
Definition runtime_command_code(k:runtime_command)tail:=
 match k with
 |Rcmp x=>succM M(P O(P x tail))
 |Rdrop=>succM M(P(N 1)(P O tail))
 |Rnip=>succM M(P(N 2)(P O tail))
 |Rax c x y u=>succM M(P(addM M c(N 3))(P x(P y(P u tail))))
 end.
Fixpoint runtime_program(L:list runtime_command)tail:=
 match L with []=>tail|k::L=>runtime_command_code k(runtime_program L tail)end.
Definition runtime_step(k:runtime_command)(q:runtime_registers):option runtime_registers:=
 let '(t,w,d,h):=q in match k with
 |Rcmp x=>Some(if E(runtime_wim t(addM M d x))h
    then(addM M d x,P O w,addM M d x,O)else(O,w,addM M d x,O))
 |Rdrop=>Some(h,P t w,d,h)
 |Rnip=>if E h(N 1)then None else Some(t,snd(U w),d,fst(U w))
 |Rax c x y u=>Some(runtime_gate(addM M d x)(addM M h y)c,
    runtime_stack(addM M d x)h(addM M h y)c u t w,O,O)
 end.
Fixpoint runtime_exec(L:list runtime_command)(q:runtime_registers):option runtime_registers:=
 match L with []=>Some q|k::L=>match runtime_step k q with
 |Some q'=>runtime_exec L q'|None=>None end end.
Lemma runtime_code2 tag x tail:command2_graph M tag x tail(succM M(P tag(P x tail))).
Proof. exists(P tag(P x tail)),(P x tail);repeat split;auto. Qed.
Lemma runtime_code4 c x y u tail:
 command4_graph M c x y u tail(runtime_command_code(Rax c x y u)tail).
Proof. exists(P u tail),(P y(P u tail));repeat split;auto;apply runtime_code2. Qed.

Theorem runtime_step_sound k q q' tail np:
 runtime_step k q=Some q'->
 enumerator_step M(runtime_state(runtime_command_code k tail)np q)(runtime_state tail np q').
Proof.
 destruct q as[[[t w]d]h];destruct k as[x| | |c x y u];cbn [runtime_step].
 - destruct(E(runtime_wim t(addM M d x))h)eqn:Htest;intro H;inversion H;subst q'.
   + apply command_mp_success;[apply runtime_code2| |apply HP].
     apply HE in Htest. unfold search_implication. rewrite <-Htest. apply runtime_value_graph.
   + apply command_mp_failure;[apply runtime_code2|].
     apply runtime_eq_false in Htest. intro Hi;apply Htest.
     eapply code_relation_functional;[apply runtime_value_graph|exact Hi].
 - intro H;inversion H;subst q'. apply command_drop_step;[apply runtime_code2|apply HP].
 - destruct(E h(N 1))eqn:Htest;intro H;[discriminate|]. inversion H;subst q'.
   apply command_nip_step;[apply runtime_code2|now apply runtime_eq_false|apply HU].
 - intro H;inversion H;subst q'. eapply (command_ax_step M c x y u tail _ np t w d h _ _).
   + apply runtime_code4.
   + apply runtime_value_graph.
   + apply runtime_gate_spec.
Qed.
Theorem runtime_step_halt k q tail np:runtime_step k q=None->
 enumerator_halt M(runtime_state(runtime_command_code k tail)np q).
Proof.
 destruct q as[[[t w]d]h];destruct k;cbn [runtime_step];try discriminate.
 destruct(E h(N 1))eqn:Htest;[|discriminate]. intros _.
 apply HE in Htest;subst h. eapply(command_nip_halt M tail _ np t w d);apply runtime_code2.
Qed.

Theorem runtime_exec_reaches L q q' tail np:runtime_exec L q=Some q'->
 numerical_reaches M(runtime_state(runtime_program L tail)np q)(runtime_state tail np q').
Proof.
 induction L as[|k L IH]in q|-*;cbn [runtime_exec runtime_program].
 - intro H;inversion H;subst q'. apply numerical_reaches_reflexive.
 - destruct(runtime_step k q)as[r|]eqn:Hs;[|discriminate]. intro H.
   eapply numerical_reaches_transitive with(t:=runtime_state(runtime_program L tail)np r).
   + apply numerical_reaches_step. exact(runtime_step_sound k q r(runtime_program L tail)np Hs).
   + now apply IH.
Qed.
Theorem runtime_exec_halts L q tail np:runtime_exec L q=None->
 numerical_halts_from M(runtime_state(runtime_program L tail)np q).
Proof.
 induction L as[|k L IH]in q|-*;cbn [runtime_exec runtime_program];[discriminate|].
 destruct(runtime_step k q)as[r|]eqn:Hs;intro H.
 - eapply numerical_reaches_halts with(t:=runtime_state(runtime_program L tail)np r).
   + apply numerical_reaches_step. exact(runtime_step_sound k q r(runtime_program L tail)np Hs).
   + now apply IH.
 - apply numerical_halts_immediate. exact(runtime_step_halt k q(runtime_program L tail)np Hs).
Qed.
End Runtime.

Print Assumptions numerical_runtime_operations.
Print Assumptions runtime_exec_reaches.
Print Assumptions runtime_exec_halts.









