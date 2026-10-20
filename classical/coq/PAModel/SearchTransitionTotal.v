(** Exact local totality of the numerical enumerator in every PA model. *)
From PAModel Require Import Model Arithmetic FiniteCoding Pairing CodeExpressions SearchStep.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Logic.Classical_Prop.
Unset Implicit Arguments.

Section Totality.
Variable M : Model.
Local Notation D := (carrier M).
Local Notation O := (zeroM M).
Local Notation S := (succM M).
Local Notation N := (code_numeral M).
Local Definition PA := fun ax H rho => axioms M ax rho H.

Lemma numerical_search_prefix_total (s : search_state D) :
  exists pl1 np1 ac pl2 x pl3 d1,
    search_prefix_relation M s pl1 np1 ac pl2 x pl3 d1.
Proof.
  destruct (@Peano.zero_or_succ D (raw_interpretation M) PA (search_pl s))
    as [Hz|[p Hp]].
  - destruct (pair_surjective M (search_np s)) as [ac [pl2 H1]].
    destruct (pair_surjective M pl2) as [x [pl3 H2]].
    exists (search_np s),(S (search_np s)),ac,pl2,x,pl3,
      (addM M (search_d s) x).
    split; [left; split; [exact Hz|split; [reflexivity|]]|].
    + apply search_add_graph_correct. cbn [code_numeral].
      apply succ_as_add.
    + split; [now apply search_pair_graph_correct|].
      split; [now apply search_pair_graph_correct|].
      apply search_add_graph_correct. reflexivity.
  - destruct (pair_surjective M p) as [ac [pl2 H1]].
    destruct (pair_surjective M pl2) as [x [pl3 H2]].
    exists p,(search_np s),ac,pl2,x,pl3,(addM M (search_d s) x).
    split; [right; split; [|reflexivity]|].
    + apply search_add_graph_correct. rewrite Hp. cbn [code_numeral].
      apply succ_as_add.
    + split; [now apply search_pair_graph_correct|].
      split; [now apply search_pair_graph_correct|].
      apply search_add_graph_correct. reflexivity.
Qed.

Lemma numerical_search_kernel_total (s : search_state D) pl3 np1 ac d1 :
  (exists t, search_kernel_relation M s t pl3 np1 ac d1) \/
  (ac=N 2 /\ search_h s=N 1).
Proof.
  destruct (@Peano.zero_or_succ D (raw_interpretation M) PA ac) as [E0|[a E1]].
  - subst ac. left.
    destruct (classic (search_implication M (search_tw s) d1 (search_h s))) as [Hi|Hi].
    + destruct (pair_total M O (search_ws s)) as [w Hw].
      exists (mkSearchState D pl3 np1 d1 w d1 O).
      left. cbn. split; [reflexivity|]. split; [repeat split|]. split; [reflexivity|].
      left. split; [exact Hi|]. split; [reflexivity|]. now apply search_pair_graph_correct.
    + exists (mkSearchState D pl3 np1 O (search_ws s) d1 O).
      left. cbn. split; [reflexivity|]. split; [repeat split|]. split; [reflexivity|].
      right. auto.
  - destruct (@Peano.zero_or_succ D (raw_interpretation M) PA a) as [E0|[b E2]].
    + subst a ac. left.
      destruct (pair_total M (search_tw s) (search_ws s)) as [w Hw].
      exists (mkSearchState D pl3 np1 (search_h s) w d1 (search_h s)).
      right; left. cbn. split; [reflexivity|]. split; [repeat split|].
      split; [reflexivity|]. split; [now apply search_pair_graph_correct|reflexivity].
    + destruct (@Peano.zero_or_succ D (raw_interpretation M) PA b) as [E0|[c E3]].
      * subst b a ac.
        destruct (classic (search_h s=N 1)) as [Hh|Hh].
        -- right. auto.
        -- left. destruct (pair_surjective M (search_ws s)) as [h [w Hw]].
           exists (mkSearchState D pl3 np1 (search_tw s) w d1 h).
           right; right; left. cbn. split; [reflexivity|]. split; [exact Hh|].
           split; [repeat split|]. split; [reflexivity|]. now apply search_pair_graph_correct.
      * subst b a ac. left.
        destruct (pair_surjective M pl3) as [y [pl4 H4]].
        destruct (pair_surjective M pl4) as [u [pl5 H5]].
        set (bb := addM M (search_h s) y).
        destruct (code_relation_total M (E_ax_stack (CEvar 0) (CEvar 1) (CEvar 2)
          (CEvar 3) (CEvar 4) (CEvar 5) (CEvar 6))
          (search_values M (d1 :: search_h s :: bb :: c :: u :: search_tw s :: search_ws s :: nil)))
          as [w Hw].
        assert (Hac : search_add_graph M c (N 3) (S (S (S c)))).
        { apply search_add_graph_correct. cbn [code_numeral].
          rewrite (Arithmetic.add_comm M c (S (S (S O)))), !(Arithmetic.add_succ M), (Arithmetic.add_zero M). reflexivity. }
        destruct (classic (c=d1 \/ c=bb)) as [Hg|Hg].
        -- exists (mkSearchState D pl5 np1 O w O O).
           right; right; right. exists c,y,pl4,u,pl5,bb.
           split; [exact Hac|]. split; [now apply search_pair_graph_correct|].
           split; [now apply search_pair_graph_correct|]. split.
           ++ apply search_add_graph_correct. reflexivity.
           ++ cbn. repeat split; try reflexivity.
              ** exact Hw.
              ** left. auto.
        -- destruct (code_relation_total M (E_bundle (CEvar 0) (CEvar 1) (CEvar 2))
             (search_values M (d1 :: bb :: c :: nil))) as [v Hv].
           exists (mkSearchState D pl5 np1 v w O O).
           right; right; right. exists c,y,pl4,u,pl5,bb.
           split; [exact Hac|]. split; [now apply search_pair_graph_correct|].
           split; [now apply search_pair_graph_correct|]. split.
           ++ apply search_add_graph_correct. reflexivity.
           ++ cbn. repeat split; try reflexivity.
              ** exact Hw.
              ** right. split; [tauto|]. split; [tauto|exact Hv].
Qed.

Theorem numerical_search_step_or_halt (s : search_state D) :
  (exists t, enumerator_step M s t) \/ enumerator_halt M s.
Proof.
  destruct (numerical_search_prefix_total s) as
    [pl1 [np1 [ac [pl2 [x [pl3 [d1 Hp]]]]]]].
  destruct (numerical_search_kernel_total s pl3 np1 ac d1) as [[t Ht]|[Ha Hh]].
  - left. exists t. exists pl1,np1,ac,pl2,x,pl3,d1. auto.
  - right. exists pl1,np1,ac,pl2,x,pl3,d1. auto.
Qed.
End Totality.

Print Assumptions numerical_search_prefix_total.
Print Assumptions numerical_search_step_or_halt.


