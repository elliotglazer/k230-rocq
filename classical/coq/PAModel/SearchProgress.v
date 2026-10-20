(** Exact candidate-counter and program-tail progress, for internal states. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT Pairing
  CodeExpressions CodeDescent SearchStep SearchTransitionTotal.
From Stdlib Require Import setoid_ring.Ring.
Unset Implicit Arguments.

Section Progress.
Variable M : Model.
Local Notation D := (carrier M).
Local Notation O := (zeroM M).
Local Notation S := (succM M).
Local Infix "+" := (addM M).
Add Ring search_progress_ring : (model_semiring M).

Lemma search_pair_tail_bound a b p : search_pair_graph M a b p ->
  exists d, p=b+d.
Proof. intro H. apply search_pair_graph_correct in H.
  exact (proj2 (pair_coordinate_bounds M a b p H)). Qed.

Lemma numerical_step_progress s t : enumerator_step M s t ->
  exists pl1 np1,
    ((search_pl s=O /\ pl1=search_np s /\ np1=S (search_np s)) \/
     (search_pl s=S pl1 /\ np1=search_np s)) /\
    search_np t=np1 /\ exists delta, pl1=search_pl t+delta.
Proof.
  intros [pl1 [np1 [ac [pl2 [x [pl3 [d1 [Hp Hk]]]]]]]].
  destruct Hp as [Hcase [H12 [H23 Hd]]].
  destruct (search_pair_tail_bound ac pl2 pl1 H12) as [d12 E12].
  destruct (search_pair_tail_bound x pl3 pl2 H23) as [d23 E23].
  exists pl1,np1. split.
  - destruct Hcase as [[Hz [Hpl Hnp]]|[Hpl Hnp]].
    + left. split; [exact Hz|]. split; [exact Hpl|].
      apply search_add_graph_correct in Hnp.
      change (np1=search_np s+S O) in Hnp.
      now rewrite <-(succ_as_add M (search_np s)) in Hnp.
    + right. split; [|exact Hnp]. apply search_add_graph_correct in Hpl.
      change (search_pl s=pl1+S O) in Hpl.
      now rewrite <-(succ_as_add M pl1) in Hpl.
  - destruct Hk as [[_ [[Ht Hnp] _]]|[[_ [[Ht Hnp] _]]|[[_ [_ [[Ht Hnp] _]]]|Hax]]].
    + split; [exact (proj1 Hnp)|]. exists (d23+d12). rewrite Ht,E12,E23. ring.
    + split; [exact (proj1 Hnp)|]. exists (d23+d12). rewrite Ht,E12,E23. ring.
    + split; [exact (proj1 Hnp)|]. exists (d23+d12). rewrite Ht,E12,E23. ring.
    + destruct Hax as [c [y [pl4 [u [pl5 [b [_ [H34 [H45 [_ [Ht [Hnp _]]]]]]]]]]]].
      split; [exact Hnp|].
      destruct (search_pair_tail_bound y pl4 pl3 H34) as [d34 E34].
      destruct (search_pair_tail_bound u pl5 pl4 H45) as [d45 E45].
      exists (d45+d34+d23+d12). rewrite Ht,E12,E23,E34,E45. ring.
Qed.

Lemma numerical_step_positive_decreases s t p :
  search_pl s=S p -> enumerator_step M s t ->
  coding_lt M (search_pl t) (search_pl s) /\ search_np t=search_np s.
Proof.
  intros Hpos Hstep. destruct (numerical_step_progress s t Hstep)
    as [pl1 [np1 [Hcase [Hnp [d Ed]]]]].
  destruct Hcase as [[Hz _]|[Hp Hn]].
  - exfalso. apply (zero_ne_succ M p). congruence.
  - split; [|congruence]. exists d. now rewrite Hp,Ed.
Qed.

Lemma numerical_step_new_candidate s t :
  search_pl s=O -> enumerator_step M s t ->
  search_np t=S (search_np s) /\
  coding_lt M (search_pl t) (S (search_np s)).
Proof.
  intros Hz Hstep. destruct (numerical_step_progress s t Hstep)
    as [pl1 [np1 [Hcase [Hnp [d Ed]]]]].
  destruct Hcase as [[_ [Hpl Hn]]|[Hp _]].
  - split; [congruence|]. exists d. now rewrite <-Hpl,Ed.
  - exfalso. apply (zero_ne_succ M pl1). congruence.
Qed.
End Progress.

Print Assumptions numerical_step_progress.
Print Assumptions numerical_step_positive_decreases.
