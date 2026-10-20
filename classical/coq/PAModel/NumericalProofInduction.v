(** Induction on an internally coded Hilbert proof in any PA model.
    The invariant must be PA-definable. No external well-foundedness of
    the model order and no standardness of a proof length are assumed. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  CodeExpressions NumericalProofs CourseOfValues.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Definition proof_line_invariant_formula (theta : form) : form :=
  ∀ (numerical_derivation_formula $2 $3 $1 $0 →
    theta[($0 .: fun i => var (S (S (S (S i)))))]).

Lemma proof_line_invariant_rebase M theta rho v i b c :
  holds M (v .: i .: b .: c .: rho)
    theta[($0 .: fun j => var (S (S (S (S j)))))] <->
  holds M (v .: rho) theta.
Proof.
  unfold holds. rewrite sat_comp. apply sat_ext.
  intros [|j]; reflexivity.
Qed.

Lemma numerical_proof_line_invariant_definable M (P : carrier M -> Prop) b c :
  Definable1 M P ->
  Definable1 M (fun i => forall v, numerical_derivation M b c i v -> P v).
Proof.
  intros [theta [rho HP]].
  exists (proof_line_invariant_formula theta),(b .: c .: rho).
  intro i. unfold proof_line_invariant_formula. rewrite holds_all.
  split.
  - intros H v. rewrite holds_imp,numerical_derivation_formula_correct.
    rewrite proof_line_invariant_rebase.
    change (numerical_derivation M b c i v -> holds M (v .: rho) theta).
    rewrite <- (HP v). exact (H v).
  - intros H v Hv. specialize (H v).
    rewrite holds_imp,numerical_derivation_formula_correct,
      proof_line_invariant_rebase in H.
    apply (proj2 (HP v)). exact (H Hv).
Qed.

Lemma numerical_derivation_prefix M b c n f i v :
  numerical_derivation M b c n f -> coding_lt M i n ->
  beta M b c i v -> numerical_derivation M b c i v.
Proof.
  intros [Hseq Hlast] Hin Hvalue. split; [|exact Hvalue].
  intros j w Hji Hw. apply Hseq; [|exact Hw].
  apply coding_lt_succ_cases. left.
  destruct (proj1 (coding_lt_succ_cases M j i) Hji) as [Hlt|E].
  - exact (coding_lt_trans M j i n Hlt Hin).
  - subst j. exact Hin.
Qed.

Theorem numerical_proof_induction M (P : carrier M -> Prop) :
  Definable1 M P ->
  (forall f, K230_axiom_relation M f -> P f) ->
  (forall a f h, P a -> P h -> implication_graph M a f h -> P f) ->
  (forall x h f, P h -> universal_graph M x h f -> P f) ->
  forall f, numerically_provable M f -> P f.
Proof.
  intros HD HA HMP HG f [b [c [n Hder]]].
  assert (Hlines : forall i v, numerical_derivation M b c i v -> P v).
  { apply (definable_strong_induction M
      (fun i => forall v, numerical_derivation M b c i v -> P v)
      (numerical_proof_line_invariant_definable M P b c HD)).
    intros i IH v Hv.
    pose proof (proj1 Hv i v (coding_lt_succ M i) (proj2 Hv)) as Hj.
    destruct Hj as [Hax|[Hmp|Hgen]].
    - exact (HA v Hax).
    - destruct Hmp as [j [k [a [h [Hj [Hk [Hja [Hkh Himp]]]]]]]].
      apply (HMP a v h).
      + exact (IH j Hj a (numerical_derivation_prefix M b c i v j a Hv Hj Hja)).
      + exact (IH k Hk h (numerical_derivation_prefix M b c i v k h Hv Hk Hkh)).
      + exact Himp.
    - destruct Hgen as [j [x [h [Hj [Hh Hgen]]]]].
      apply (HG x h v); [|exact Hgen].
      exact (IH j Hj h (numerical_derivation_prefix M b c i v j h Hv Hj Hh)). }
  exact (Hlines n f Hder).
Qed.

Print Assumptions proof_line_invariant_rebase.
Print Assumptions numerical_proof_line_invariant_definable.
Print Assumptions numerical_derivation_prefix.
Print Assumptions numerical_proof_induction.
