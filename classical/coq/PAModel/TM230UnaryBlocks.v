(** Arithmetic words for the exact unary register representation.
    The head cell is the least significant bit. No finite-model or
    standard-exponent restriction is imposed. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
 PowerTwoSyntax PowerTwoRecurrence PowerTwoPositive PowerTwoLaws.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import setoid_ring.Ring.
Unset Implicit Arguments.

Definition machine230_unary_block M value tail word : Prop :=
 exists p k,power2 M(succM M value)p /\ p=succM M k /\
 word=addM M(mulM M(code_numeral M 2)k)
   (mulM M(mulM M(code_numeral M 2)p)tail).

Definition machine230_marked_block M value tail word : Prop :=
 exists p k,power2 M value p /\ p=succM M k /\
 word=addM M(mulM M(code_numeral M 4)k)
   (mulM M(mulM M(code_numeral M 4)p)tail).

Section Arithmetic.
Variable M:Model.
Local Notation D := (carrier M).
Local Notation Z := (zeroM M).
Local Notation S := (succM M).
Local Notation two := (code_numeral M 2).
Local Notation four := (code_numeral M 4).
Local Infix "+" := (addM M).
Local Infix "*" := (mulM M).
Add Ring unary_block_ring:(model_semiring M).
Lemma unary_two:two=S Z+S Z.
Proof. apply succ_as_add. Qed.
Lemma unary_four:four=(S Z+S Z)+(S Z+S Z).
Proof.
 change(S(S(S(S Z)))=(S Z+S Z)+(S Z+S Z)).
 rewrite(succ_as_add M(S(S(S Z)))),(succ_as_add M(S(S Z))),
   (succ_as_add M(S Z)). ring.
Qed.

Theorem machine230_unary_block_total value tail :
 exists word,machine230_unary_block M value tail word.
Proof.
 destruct(power2_total M(S value))as[p Hp].
 destruct(power2_positive_successor M(S value)p Hp)as[k Hk].
 exists(two*k+two*p*tail),p,k. auto.
Qed.
Theorem machine230_unary_block_functional value tail x y :
 machine230_unary_block M value tail x ->machine230_unary_block M value tail y ->x=y.
Proof.
 intros[p[k[Hp[Hk Ex]]]][q[j[Hq[Hj Ey]]]].
 assert(Ep:p=q)by(eapply power2_functional;eassumption). subst q.
 assert(Ek:k=j)by(apply(succ_injective M);congruence). subst j;congruence.
Qed.
Theorem machine230_marked_block_total value tail :
 exists word,machine230_marked_block M value tail word.
Proof.
 destruct(power2_total M value)as[p Hp].
 destruct(power2_positive_successor M value p Hp)as[k Hk].
 exists(four*k+four*p*tail),p,k. auto.
Qed.
Theorem machine230_marked_block_functional value tail x y :
 machine230_marked_block M value tail x ->machine230_marked_block M value tail y ->x=y.
Proof.
 intros[p[k[Hp[Hk Ex]]]][q[j[Hq[Hj Ey]]]].
 assert(Ep:p=q)by(eapply power2_functional;eassumption). subst q.
 assert(Ek:k=j)by(apply(succ_injective M);congruence). subst j;congruence.
Qed.

Theorem machine230_unary_block_successor_intro value tail word :
 machine230_unary_block M value tail word ->
 machine230_unary_block M(S value)tail(two*word+two).
Proof.
 intros[p[k[Hp[Hk Eword]]]].
 exists(two*p),(S(two*k)). split;[now apply power2_successor|].
 split.
 - rewrite Hk,(succ_as_add M(S(two*k))),(succ_as_add M(two*k)),(succ_as_add M k),unary_two. ring.
 - rewrite Eword,(succ_as_add M(two*k)),?unary_four,unary_two. ring.
Qed.
Theorem machine230_unary_block_successor value tail old new :
 machine230_unary_block M value tail old ->
 (machine230_unary_block M(S value)tail new <->new=two*old+two).
Proof.
 intro Hold. split.
 - intro Hnew. eapply machine230_unary_block_functional;[exact Hnew|].
   now apply machine230_unary_block_successor_intro.
 - intro Enew. rewrite Enew. now apply machine230_unary_block_successor_intro.
Qed.

Theorem machine230_marked_block_plain value tail marked :
 machine230_marked_block M value tail marked ->
 machine230_unary_block M value tail(marked+two).
Proof.
 intros[p[k[Hp[Hk Eword]]]].
 exists(two*p),(S(two*k)). split;[now apply power2_successor|].
 split.
 - rewrite Hk,(succ_as_add M(S(two*k))),(succ_as_add M(two*k)),(succ_as_add M k),unary_two. ring.
 - rewrite Eword,(succ_as_add M(two*k)),?unary_four,unary_two. ring.
Qed.
Theorem machine230_plain_marked_difference value tail plain marked :
 machine230_unary_block M value tail plain ->
 machine230_marked_block M value tail marked ->plain=marked+two.
Proof.
 intros Hplain Hmarked. eapply machine230_unary_block_functional;[exact Hplain|].
 now apply machine230_marked_block_plain.
Qed.
Theorem machine230_unary_block_has_mark value tail plain :
 machine230_unary_block M value tail plain ->
 exists marked,machine230_marked_block M value tail marked /\ plain=marked+two.
Proof.
 intro H. destruct(machine230_marked_block_total value tail)as[marked HM].
 exists marked. split;[exact HM|]. exact(machine230_plain_marked_difference value tail plain marked H HM).
Qed.
Theorem machine230_unary_block_zero tail word :
 machine230_unary_block M Z tail word <->word=two+four*tail.
Proof.
 assert(Hblock:machine230_unary_block M Z tail(two+four*tail)).
 { exists two,(S Z). split.
   - replace two with(two*S Z)by ring. exact(power2_successor M Z(S Z)(power2_zero M)).
   - split;[reflexivity|]. rewrite ?unary_four,?unary_two. ring. }
 split;[intro H;eapply machine230_unary_block_functional;eassumption|].
 intro E. now rewrite E.
Qed.
Theorem machine230_marked_block_zero tail word :
 machine230_marked_block M Z tail word <->word=four*tail.
Proof.
 assert(Hblock:machine230_marked_block M Z tail(four*tail)).
 { exists(S Z),Z. split;[apply power2_zero|]. split;[reflexivity|].
   rewrite ?unary_four,?unary_two. ring. }
 split;[intro H;eapply machine230_marked_block_functional;eassumption|].
 intro E. now rewrite E.
Qed.
End Arithmetic.
Print Assumptions machine230_unary_block_total.
Print Assumptions machine230_unary_block_successor.
Print Assumptions machine230_plain_marked_difference.
