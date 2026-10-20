(** Closure for an arbitrary PA-definable numerical axiom predicate.
    The beta certificates may have nonstandard length. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  BetaExtension BetaPacking CodeExpressions NumericalProofs NumericalTheories.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import setoid_ring.Ring.
Unset Implicit Arguments.

Section TheoryClosure.
Variable M : Model.
Variable T : NumericalTheory.
Local Notation D := (carrier M).
Local Notation O := (zeroM M).
Local Notation S := (succM M).
Local Infix "+" := (addM M).
Add Ring closure_ring : (model_semiring M).

Definition theory_prefix b c b' c' n : Prop :=
  forall i v, coding_lt M i n -> beta M b c i v -> beta M b' c' i v.

Lemma theory_prefix_back b c b' c' n : theory_prefix b c b' c' n ->
  forall i v, coding_lt M i n -> beta M b' c' i v -> beta M b c i v.
Proof.
  intros H i v Hi Hv. destruct (beta_total M b c i) as [u Hu].
  assert (u=v) by (eapply beta_unique; [exact (H i u Hi Hu)|exact Hv]).
  now subst u.
Qed.

Lemma theory_justified_transport b c b' c' i i' (f : D -> D) v :
  (forall j, coding_lt M j i -> coding_lt M (f j) i') ->
  (forall j t, coding_lt M j i -> beta M b c j t -> beta M b' c' (f j) t) ->
  theory_justified M T b c i v -> theory_justified M T b' c' i' v.
Proof.
  intros Hlt Hr [Ha|[Hp|Hg]].
  - now left.
  - right; left. destruct Hp as [j [k [t [u [Hj [Hk [Ht [Hu Himp]]]]]]]].
    exists (f j),(f k),t,u.
    split; [now apply Hlt|]. split; [now apply Hlt|].
    split; [now apply Hr|]. split; [now apply Hr|exact Himp].
  - right; right. destruct Hg as [j [a [h [Hj [Hh Hall]]]]].
    exists (f j),a,h. split; [now apply Hlt|].
    split; [now apply Hr|exact Hall].
Qed.

Lemma theory_proof_sequence_transfer b c b' c' n :
  theory_prefix b c b' c' n -> theory_proof_sequence M T b c n -> theory_proof_sequence M T b' c' n.
Proof.
  intros Hp Hseq i v Hi Hv.
  apply (theory_justified_transport b c b' c' i i (fun j => j) v).
  - auto.
  - intros j t Hj Ht. apply Hp; [eapply coding_lt_trans; eassumption|exact Ht].
  - apply Hseq; [exact Hi|]. exact (theory_prefix_back b c b' c' n Hp i v Hi Hv).
Qed.

Lemma theory_proof_sequence_append b c b' c' n v :
  theory_proof_sequence M T b c n -> theory_prefix b c b' c' n ->
  beta M b' c' n v -> theory_justified M T b' c' n v ->
  theory_proof_sequence M T b' c' (S n).
Proof.
  intros Hseq Hp Hv Hj i u Hi Hu.
  destruct (proj1 (coding_lt_succ_cases M i n) Hi) as [Hin | ->].
  - exact (theory_proof_sequence_transfer b c b' c' n Hp Hseq i u Hin Hu).
  - assert (u=v) by (eapply beta_unique; eassumption). now subst u.
Qed.

Theorem theory_numerical_axiom f : theory_axiom M T f -> theory_provable M T f.
Proof.
  intro Ha. exists f,f,O. split; [|apply beta_singleton].
  intros i v Hi Hv.
  destruct (proj1 (coding_lt_succ_cases M i O) Hi) as [Hin | ->].
  - exfalso. exact (coding_not_lt_zero M i Hin).
  - assert (v=f) by (eapply beta_unique; [exact Hv|apply beta_singleton]).
    subst v. now left.
Qed.

Theorem theory_numerical_gen a h v :
  theory_provable M T h -> universal_graph M a h v -> theory_provable M T v.
Proof.
  intros [b [c [n [Hseq Hh]]]] Hall.
  destruct (beta_extension M b c (S n) v) as [b' [c' [Hp Hv]]].
  exists b',c',(S n). split; [|exact Hv].
  apply (theory_proof_sequence_append b c b' c' (S n) v Hseq Hp Hv).
  right; right. exists n,a,h. split; [apply coding_lt_succ|].
  split; [apply Hp; [apply coding_lt_succ|exact Hh]|exact Hall].
Qed.

Lemma theory_lt_add_cancel l i j : coding_lt M (l+i) (l+j) -> coding_lt M i j.
Proof.
  intros [d Hd]. exists d.
  apply (Arithmetic.add_cancel M j (S (i+d)) l).
  rewrite (Arithmetic.add_comm M j l), Hd.
  rewrite (succ_as_add M ((l+i)+d)), (succ_as_add M (i+d)). ring.
Qed.

Lemma theory_lt_left_sum i l n : coding_lt M i l -> coding_lt M i (l+n).
Proof.
  intros Hi. apply (@Peano.lt_le_trans D (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) i (l+n) l Hi).
  exists n. reflexivity.
Qed.

Lemma theory_proof_sequence_concatenate b c l d e n b' c' :
  theory_proof_sequence M T b c l -> theory_proof_sequence M T d e n ->
  theory_prefix b c b' c' l ->
  (forall j v, coding_lt M j n -> beta M d e j v -> beta M b' c' (l+j) v) ->
  theory_proof_sequence M T b' c' (l+n).
Proof.
  intros Hleft Hright Hl Hr i v Hi Hv.
  destruct (@Peano.trichotomy D (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) i l) as [Hil|[Hil|Hil]].
  - exact (theory_proof_sequence_transfer b c b' c' l Hl Hleft i v Hil Hv).
  - assert (Hne : ~coding_lt M i l).
    { intro H. exact (@Peano.lt_neq D (raw_interpretation M)
        (fun ax H rho => axioms M ax rho H) i l H Hil). }
    destruct (coding_difference M i l Hne) as [j ->].
    assert (Hj : coding_lt M j n) by (eapply theory_lt_add_cancel; exact Hi).
    destruct (beta_total M d e j) as [u Hu].
    assert (E : u=v) by (eapply beta_unique; [exact (Hr j u Hj Hu)|exact Hv]).
    subst u. apply (theory_justified_transport d e b' c' j (l+j) (fun k => l+k) v).
    + intros k Hk. now apply coding_lt_add_left.
    + intros k t Hk Ht. apply Hr; [eapply coding_lt_trans; eassumption|exact Ht].
    + exact (Hright j v Hj Hu).
  - assert (Hne : ~coding_lt M i l).
    { intro H.
      pose proof (coding_lt_trans M i l i H Hil) as Hii.
      exact (@Peano.lt_neq D (raw_interpretation M)
        (fun ax H rho => axioms M ax rho H) i i Hii eq_refl). }
    destruct (coding_difference M i l Hne) as [j ->].
    assert (Hj : coding_lt M j n) by (eapply theory_lt_add_cancel; exact Hi).
    destruct (beta_total M d e j) as [u Hu].
    assert (E : u=v) by (eapply beta_unique; [exact (Hr j u Hj Hu)|exact Hv]).
    subst u. apply (theory_justified_transport d e b' c' j (l+j) (fun k => l+k) v).
    + intros k Hk. now apply coding_lt_add_left.
    + intros k t Hk Ht. apply Hr; [eapply coding_lt_trans; eassumption|exact Ht].
    + exact (Hright j v Hj Hu).
Qed.

Theorem theory_numerical_mp a b h :
  theory_provable M T a -> theory_provable M T h ->
  implication_graph M a b h -> theory_provable M T b.
Proof.
  intros [p [q [i [Hi Ha]]]] [r [s [j [Hj Hh]]]] Himp.
  destruct (beta_concatenate M p q (S i) r s (S j)) as [t [u [Hl Hr]]].
  set (n := S i + S j).
  assert (Hseq : theory_proof_sequence M T t u n).
  { apply (theory_proof_sequence_concatenate p q (S i) r s (S j) t u Hi Hj Hl Hr). }
  assert (Hin : coding_lt M i n).
  { apply theory_lt_left_sum. apply coding_lt_succ. }
  assert (Hjn : coding_lt M (S i+j) n).
  { apply coding_lt_add_left. apply coding_lt_succ. }
  assert (Hat : beta M t u i a) by (apply Hl; [apply coding_lt_succ|exact Ha]).
  assert (Hht : beta M t u (S i+j) h) by (apply Hr; [apply coding_lt_succ|exact Hh]).
  destruct (beta_extension M t u n b) as [t' [u' [Hp Hb]]].
  exists t',u',n. split; [|exact Hb].
  apply (theory_proof_sequence_append t u t' u' n b Hseq Hp Hb).
  right; left. exists i,(S i+j),a,h.
  split; [exact Hin|]. split; [exact Hjn|].
  split; [exact (Hp i a Hin Hat)|].
  split; [exact (Hp (S i+j) h Hjn Hht)|exact Himp].
Qed.

End TheoryClosure.
