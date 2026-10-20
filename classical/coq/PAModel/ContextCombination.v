(** Combining internally finite assumption contexts. This construction is
    used to put source assumptions and domain assumptions in one context. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaPacking
  NumericalEnvironments NumericalContexts ContextualProofs.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import setoid_ring.Ring.
Unset Implicit Arguments.

Section Combination.
Variable M : Model.
Local Infix "+" := (addM M).
Local Notation S := (succM M).
Add Ring context_combination_ring : (model_semiring M).

Lemma context_lt_add_cancel_left n i j : coding_lt M (n+i) (n+j) -> coding_lt M i j.
Proof.
  intros [d Hd]. exists d.
  apply (Arithmetic.add_cancel M j (S (i+d)) n).
  replace (j+n) with (n+j) by ring.
  replace (S (i+d)+n) with (S ((n+i)+d)).
  - exact Hd.
  - rewrite (succ_as_add M (i+d)),(succ_as_add M ((n+i)+d)). ring.
Qed.

Definition context_union b c n d e m u v l :=
  l=n+m /\ forall f,
    context_member M u v l f <-> context_member M b c n f \/ context_member M d e m f.

Theorem context_union_total b c n d e m : exists u v l, context_union b c n d e m u v l.
Proof.
  destruct (beta_concatenate M b c n d e m) as [u [v [HL HR]]].
  exists u,v,(n+m). split; [reflexivity|]. intro f. split.
  - intros [i [Hi Hf]]. destruct (environment_lt_cases M i n) as [Hin|Hin].
    + left. destruct (beta_total M b c i) as [g Hg].
      assert (f=g) by (exact (beta_unique M u v i f g Hf (HL i g Hin Hg))).
      subst g. exists i. auto.
    + right. destruct (coding_difference M i n Hin) as [j ->].
      pose proof (context_lt_add_cancel_left n j m Hi) as Hj.
      destruct (beta_total M d e j) as [g Hg].
      assert (f=g) by (exact (beta_unique M u v (n+j) f g Hf (HR j g Hj Hg))).
      subst g. exists j. auto.
  - intros [[i [Hi Hf]]|[j [Hj Hf]]].
    + exists i. split; [|exact (HL i f Hi Hf)].
      apply (@Peano.lt_le_trans (carrier M) (raw_interpretation M)
        (fun ax H rho => axioms M ax rho H) i (n+m) n Hi).
      exists m. reflexivity.
    + exists (n+j). split.
      * exact (coding_lt_add_left M n j m Hj).
      * exact (HR j f Hj Hf).
Qed.

Theorem context_union_left b c n d e m u v l :
  context_union b c n d e m u v l -> context_included M b c n u v l.
Proof. intros [_ H] f Hf. apply (proj2 (H f)). now left. Qed.

Theorem context_union_right b c n d e m u v l :
  context_union b c n d e m u v l -> context_included M d e m u v l.
Proof. intros [_ H] f Hf. apply (proj2 (H f)). now right. Qed.

Theorem context_union_fresh b c n d e m u v l x :
  context_union b c n d e m u v l ->
  (context_fresh M u v l x <-> context_fresh M b c n x /\ context_fresh M d e m x).
Proof.
  intros [_ H]. split.
  - intro HF. split; intros f Hf; apply HF; apply (proj2 (H f)); auto.
  - intros [HL HR] f Hf. apply (proj1 (H f)) in Hf. destruct Hf as [Hf|Hf]; auto.
Qed.

Theorem context_union_hyp_left b c n d e m u v l f :
  context_union b c n d e m u v l -> context_member M b c n f ->
  contextually_provable M u v l f.
Proof. intros H Hf. apply contextual_hyp. exact (context_union_left b c n d e m u v l H f Hf). Qed.

Theorem context_union_hyp_right b c n d e m u v l f :
  context_union b c n d e m u v l -> context_member M d e m f ->
  contextually_provable M u v l f.
Proof. intros H Hf. apply contextual_hyp. exact (context_union_right b c n d e m u v l H f Hf). Qed.
End Combination.

Print Assumptions context_union_total.
Print Assumptions context_union_fresh.
Print Assumptions context_union_hyp_left.
Print Assumptions context_union_hyp_right.
