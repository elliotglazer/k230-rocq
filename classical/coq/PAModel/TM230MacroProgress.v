(** Positive progress follows from actual paths and distinct literal control
    states; it is not a separate simulator correctness assumption. *)
From PAModel Require Import Model FiniteCoding CodeExpressions TM230BinaryStep TM230BitArithmetic
 TM230LeftView TM230RunComposition TM230StandardPacking TM230Paths TM230SkipBlock TM230UnaryBlocks TM230RegisterPrefix TM230BoxMark.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lists.List Lia.
Unset Implicit Arguments.
Definition machine230_progresses M s t:=exists b c n,
 coding_lt M(zeroM M)n /\machine230_path M b c n s t.
Lemma machine230_numeral_injective M n m:
 code_numeral M n=code_numeral M m->n=m.
Proof.
 revert m. induction n as[|n IH];intros[|m]E;[reflexivity| | |].
 -exfalso. exact(zero_ne_succ M _ E).
 -exfalso. symmetry in E. exact(zero_ne_succ M _ E).
 -f_equal. apply IH. exact(succ_injective M _ _ E).
Qed.
Theorem machine230_reaches_progress M s t:
 machine230_state s<>machine230_state t->machine230_reaches M s t->machine230_progresses M s t.
Proof.
 intros Hne[b[c[n Hpath]]].
 destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)
  (fun ax H rho=>axioms M ax rho H)n)as[E|[k E]].
 -subst n. destruct Hpath as[[Hs Hstep]Ht].
  assert(Es:s=t)by(eapply machine230_state_at_unique;eassumption). subst t. contradiction.
 -subst n. exists b,c,(succM M k). split;[apply coding_zero_lt_succ|exact Hpath].
Qed.
Lemma machine230_skip_exit_distinct n:(n<9)%nat->machine230_skip_label n<>1 /\machine230_skip_label n<>3.
Proof. intro H. do 9(destruct n as[|n];[split;discriminate|]). lia. Qed.
Corollary machine230_box_mark_progress M prefix value left tail target word s:
 (length prefix<9)%nat ->machine230_unary_block M value tail target ->
 machine230_blocks_list M prefix target word ->
 machine230_right_view M(machine230_skip_label(length prefix))left word s ->
 exists marked t,machine230_marked_file M prefix value tail marked /\
 machine230_left_view M(machine230_return_exit 1 prefix)marked left t /\machine230_progresses M s t.
Proof.
 intros HB HT HP HS. destruct(machine230_box_mark M prefix value left tail target word s HB HT HP HS)
 as[marked[t[HM[HV HR]]]]. exists marked,t. split;[exact HM|]. split;[exact HV|].
 apply(machine230_reaches_progress M s t);[|exact HR].
 intro E. destruct HS as[HQ _],HV as[HTQ _]. rewrite HQ,HTQ in E.
 apply machine230_numeral_injective in E. destruct(machine230_skip_exit_distinct(length prefix)HB)as[H1 H3].
 destruct prefix;[exact(H1 E)|exact(H3 E)].
Qed.
Print Assumptions machine230_reaches_progress.
Print Assumptions machine230_box_mark_progress.
