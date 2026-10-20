(** Soundness of every numerical command, uniformly over PA models. *)
From PAModel Require Import Model FiniteCoding Pairing CodeExpressions
  NumericalProofs ProofClosure StackSafety SearchStep.
Unset Implicit Arguments.

Section Kernel.
Variable M : Model.
Local Notation D := (carrier M).
Local Notation O := (zeroM M).

Lemma row1 a b c u v : code_relation M (code_parameters a b c u) code_row1 v -> numerically_provable M v.
Proof. intro H. apply numerical_axiom. right. exists a,b,c,u. now left. Qed.
Lemma row2 a b c u v : code_relation M (code_parameters a b c u) code_row2 v -> numerically_provable M v.
Proof. intro H. apply numerical_axiom. right. exists a,b,c,u. right. now left. Qed.
Lemma row3 a b c u v : code_relation M (code_parameters a b c u) code_row3 v -> numerically_provable M v.
Proof. intro H. apply numerical_axiom. right. exists a,b,c,u. do 2 right. now left. Qed.
Lemma row4 a b c u v : code_relation M (code_parameters a b c u) code_row4 v -> numerically_provable M v.
Proof. intro H. apply numerical_axiom. right. exists a,b,c,u. do 3 right. now left. Qed.
Lemma row5 a b c u v : code_relation M (code_parameters a b c u) code_row5 v -> numerically_provable M v.
Proof. intro H. apply numerical_axiom. right. exists a,b,c,u. do 4 right. now left. Qed.
Lemma row6 a b c u v : code_relation M (code_parameters a b c u) code_row6 v -> numerically_provable M v.
Proof. intro H. apply numerical_axiom. right. exists a,b,c,u. do 5 right. now left. Qed.
Lemma row7 a b c u v : code_relation M (code_parameters a b c u) code_row7 v -> numerically_provable M v.
Proof. intro H. apply numerical_axiom. right. exists a,b,c,u. do 6 right. now left. Qed.
Lemma row8 a b c u v : code_relation M (code_parameters a b c u) code_row8 v -> numerically_provable M v.
Proof. intro H. apply numerical_axiom. right. exists a,b,c,u. do 7 right. now left. Qed.

Lemma bundle_provable a b c v : c <> a -> c <> b ->
  search_bundle M a b c v -> numerically_provable M v.
Proof.
  intros Ha Hb H. apply numerical_axiom. right. exists a,b,c,O.
  do 8 right. split; [exact Ha|]. split; [exact Hb|exact H].
Qed.

Definition good_code (env : nat -> D) e :=
  forall z, code_relation M env e z -> good_stack M z.
Definition provable_code (env : nat -> D) e :=
  forall z, code_relation M env e z -> numerically_provable M z.

Lemma good_code_pair env x w :
  provable_code env x -> good_code env w -> good_code env (CEpair x w).
Proof.
  intros Hx Hw z [a [b [Ha [Hb Hz]]]].
  exact (good_stack_push M a b z Hz (Hx a Ha) (Hw b Hb)).
Qed.

Lemma search_stack_good a h b c u t w z :
  numerically_provable M t -> numerically_provable M h -> good_stack M w ->
  search_stack M a h b c u t w z -> good_stack M z.
Proof.
  intros Ht Hh Hw Hstack.
  set (env := search_values M (a :: h :: b :: c :: u :: t :: w :: nil)).
  assert (HG : good_code env (E_ax_stack (CEvar 0) (CEvar 1) (CEvar 2)
    (CEvar 3) (CEvar 4) (CEvar 5) (CEvar 6))).
  { unfold E_ax_stack.
    apply good_code_pair.
    - intros v Hv. apply (row1 a b c u v). exact Hv.
    - apply good_code_pair.
      + intros v Hv. apply (row2 a b c u v). exact Hv.
      + apply good_code_pair.
        * intros v Hv. apply (row3 a b c u v). exact Hv.
        * apply good_code_pair.
          -- intros v Hv. apply (row4 a b c u v). exact Hv.
          -- apply good_code_pair.
             ++ intros v Hv. apply (row5 a b c u v). exact Hv.
             ++ apply good_code_pair.
                ** intros v Hv. apply (row6 a c O O v). exact Hv.
                ** apply good_code_pair.
                   --- intros v Hv. apply (row7 a b c u v). exact Hv.
                   --- apply good_code_pair.
                       +++ intros v Hv. apply (row8 a b c u v). exact Hv.
                       +++ apply good_code_pair.
                           *** intros v Hv. apply (numerical_gen M a h v Hh). exact Hv.
                           *** apply good_code_pair.
                               ---- intros v Hv. change (v=t) in Hv. now subst v.
                               ---- intros v Hv. change (v=w) in Hv. now subst v. }
  exact (HG z Hstack).
Qed.

Definition invariant (s : search_state D) : Prop :=
  numerically_provable M (search_tw s) /\
  numerically_provable M (search_h s) /\ good_stack M (search_ws s).

Lemma invariant_kernel s t pl3 np1 ac d1 :
  invariant s -> search_kernel_relation M s t pl3 np1 ac d1 -> invariant t.
Proof.
  intros [Ht [Hh Hw]] [Hmp|[Hdrop|[Hnip|Hax]]].
  - destruct Hmp as [_ [_ [Ecache [[Himp [Etop Epush]]|[_ [Etop Estack]]]]]].
    + split.
      * rewrite Etop. apply (numerical_mp M (search_tw s) d1 (search_h s) Ht Hh).
        exact Himp.
      * split; [rewrite Ecache; apply numerical_truth|].
        apply search_pair_graph_correct in Epush.
        exact (good_stack_push M O (search_ws s) (search_ws t) Epush (numerical_truth M) Hw).
    + split; [rewrite Etop;apply numerical_truth|].
      split; [rewrite Ecache;apply numerical_truth|now rewrite Estack].
  - destruct Hdrop as [_ [_ [Etop [Epush Ecache]]]].
    split; [now rewrite Etop|]. split; [now rewrite Ecache|].
    apply search_pair_graph_correct in Epush.
    exact (good_stack_push M (search_tw s) (search_ws s) (search_ws t) Epush Ht Hw).
  - destruct Hnip as [_ [_ [_ [Etop Epop]]]].
    apply search_pair_graph_correct in Epop.
    destruct (good_stack_pop M (search_h t) (search_ws t) (search_ws s) Epop Hw) as [Hh' Hw'].
    split; [now rewrite Etop|auto].
  - destruct Hax as [c [y [pl4 [u [pl5 [b [_ [_ [_ [_ [_ [_ [_ [Ecache [Estack Egate]]]]]]]]]]]]]]].
    split.
    + destruct Egate as [[_ Etop]|[Ha [Hb Hbundle]]].
      * rewrite Etop. apply numerical_truth.
      * exact (bundle_provable d1 b c (search_tw t) Ha Hb Hbundle).
    + split; [rewrite Ecache;apply numerical_truth|].
      exact (search_stack_good d1 (search_h s) b c u (search_tw s) (search_ws s)
        (search_ws t) Ht Hh Hw Estack).
Qed.

Theorem invariant_step s t : invariant s -> enumerator_step M s t -> invariant t.
Proof. intros Hs [pl1 [np1 [ac [pl2 [x [pl3 [d1 [_ H]]]]]]]].
  exact (invariant_kernel s t pl3 np1 ac d1 Hs H). Qed.

Theorem invariant_halt s : invariant s -> enumerator_halt M s ->
  numerically_provable M (code_numeral M 1).
Proof. intros [_ [H _]] E. now rewrite <- (enumerator_halt_cache M s E). Qed.

Definition initial_state : search_state D := mkSearchState D O O O O O O.
Lemma invariant_initial : invariant initial_state.
Proof. split; [apply numerical_truth|]. split; [apply numerical_truth|apply good_stack_zero]. Qed.

(** The literal machine's bootstrap enters this state, as pinned by Seed230.v. *)
Definition seed_state : search_state D :=
  mkSearchState D O (code_numeral M 3) O O (code_numeral M 3) O.
Lemma invariant_seed : invariant seed_state.
Proof. split; [apply numerical_truth|]. split; [apply numerical_truth|apply good_stack_zero]. Qed.

End Kernel.
