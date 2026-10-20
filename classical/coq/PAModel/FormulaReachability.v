(** Induction and extension for the existing internally finite formula paths.
    The induction invariant is required to be definable in ordinary PA. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  BetaExtension CodeExpressions NumericalProofs FreshNames TheoryProofInduction.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Section Paths.
Variable M : Model.
Local Notation O := (zeroM M).
Local Notation S := (succM M).

Theorem formula_reaches_induction (P : carrier M -> Prop) :
  Definable1 M P ->
  (forall x y, P x -> formula_edge M x y -> P y) ->
  forall f g, P f -> formula_reaches M f g -> P g.
Proof.
  intros Hdef Hstep f g Hf [b [c [n [Hfirst [Hlast Hpath]]]]].
  assert (HI : forall i, coding_lt M i (S n) ->
    forall v, beta M b c i v -> P v).
  { apply (definable_induction M _ (proof_line_property_definable M P b c n Hdef)).
    - intros _ v Hv. now rewrite (beta_unique M b c O v f Hv Hfirst).
    - intros i IH Hsi v Hv.
      assert (Hin : coding_lt M i n) by (apply coding_lt_succ_cancel; exact Hsi).
      assert (Hisn : coding_lt M i (S n)) by
        (apply coding_lt_succ_cases; now left).
      destruct (beta_total M b c i) as [u Hu].
      exact (Hstep u v (IH Hisn u Hu) (Hpath i u v Hin Hu Hv)). }
  exact (HI n (coding_lt_succ M n) g Hlast).
Qed.

Theorem formula_reaches_append_edge f a g :
  formula_reaches M f a -> formula_edge M a g -> formula_reaches M f g.
Proof.
  intros [b [c [n [Hfirst [Hlast Hpath]]]]] Hag.
  destruct (beta_extension M b c (S n) g) as [b' [c' [Hkeep Hnew]]].
  exists b',c',(S n). split.
  - exact (Hkeep O f (coding_zero_lt_succ M n) Hfirst).
  - split; [exact Hnew|].
    intros i x y Hi Hx Hy.
    destruct (proj1 (coding_lt_succ_cases M i n) Hi) as [Hin | Heq].
    + assert (Hsi : coding_lt M (S i) (S n)).
      { destruct Hin as [d Hd]. exists d. now rewrite (Arithmetic.add_succ M i d), <- Hd. }
      destruct (beta_total M b c i) as [u Hu].
      destruct (beta_total M b c (S i)) as [v Hv].
      assert (Ex : x=u) by
        (exact (beta_unique M b' c' i x u Hx (Hkeep i u Hi Hu))).
      assert (Ey : y=v) by
        (exact (beta_unique M b' c' (S i) y v Hy (Hkeep (S i) v Hsi Hv))).
      subst x y. exact (Hpath i u v Hin Hu Hv).
    + subst i. assert (Ex : x=a) by
        (exact (beta_unique M b' c' n x a Hx (Hkeep n a (coding_lt_succ M n) Hlast))).
      assert (Ey : y=g) by (exact (beta_unique M b' c' (S n) y g Hy Hnew)).
      now subst x y.
Qed.

End Paths.

Print Assumptions formula_reaches_induction.
Print Assumptions formula_reaches_append_edge.
