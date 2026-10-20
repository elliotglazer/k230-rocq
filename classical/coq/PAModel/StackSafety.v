(** A first-order arithmetic stack invariant for nonstandardly long runs. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT Pairing
  NumericalProofs ProofClosure InternalPaths.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Definition tail_edge_formula (x y : term) : form :=
  ∃ pair_formula $0 y`[↑] x`[↑].

Lemma tail_edge_formula_correct M rho x y :
  holds M rho (tail_edge_formula x y) <->
    tail_edge M (evalM M rho x) (evalM M rho y).
Proof.
  unfold tail_edge_formula, tail_edge. rewrite holds_ex.
  setoid_rewrite pair_formula_correct.
  unfold evalM. setoid_rewrite eval_up. reflexivity.
Qed.

Definition tail_path_formula (b c n : term) : form :=
  ∀∀∀ (Peano.sless $2 (lift3 n) →
    beta_formula (lift3 b) (lift3 c) $2 $1 →
    beta_formula (lift3 b) (lift3 c) (σ $2) $0 →
    tail_edge_formula $1 $0).

Local Opaque holds beta_formula Peano.sless tail_edge_formula.

Lemma tail_path_formula_correct M rho b c n :
  holds M rho (tail_path_formula b c n) <->
    tail_path M (evalM M rho b) (evalM M rho c) (evalM M rho n).
Proof.
  unfold tail_path_formula, tail_path.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite less_formula_correct.
  setoid_rewrite beta_formula_correct.
  setoid_rewrite tail_edge_formula_correct.
  setoid_rewrite lift3_correct. reflexivity.
Qed.

Definition reaches_formula (w z : term) : form :=
  ∃∃∃ (beta_formula $2 $1 zero (lift3 w) ∧
    (beta_formula $2 $1 $0 (lift3 z) ∧ tail_path_formula $2 $1 $0)).

Local Opaque tail_path_formula.

Lemma reaches_formula_correct M rho w z :
  holds M rho (reaches_formula w z) <->
    reaches M (evalM M rho w) (evalM M rho z).
Proof.
  unfold reaches_formula, reaches.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite beta_formula_correct.
  setoid_rewrite tail_path_formula_correct.
  setoid_rewrite lift3_correct. reflexivity.
Qed.

Definition good_stack M (w : carrier M) : Prop :=
  forall z h t, reaches M w z -> pair_graph M h t z -> numerically_provable M h.

Definition good_stack_formula (w : term) : form :=
  ∀∀∀ (reaches_formula (lift3 w) $2 →
    pair_formula $1 $0 $2 → numerically_provable_formula $1).

Local Opaque reaches_formula pair_formula numerically_provable_formula.

Lemma good_stack_formula_correct M rho w :
  holds M rho (good_stack_formula w) <-> good_stack M (evalM M rho w).
Proof.
  unfold good_stack_formula, good_stack.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite reaches_formula_correct.
  setoid_rewrite pair_formula_correct.
  setoid_rewrite numerically_provable_formula_correct.
  setoid_rewrite lift3_correct. reflexivity.
Qed.

Lemma good_stack_definable M : Definable1 M (good_stack M).
Proof. exists (good_stack_formula $0), (fun _ => zeroM M).
  intro w. symmetry. apply good_stack_formula_correct. Qed.

Section Safety.
Variable M : Model.
Local Notation D := (carrier M).
Local Notation O := (zeroM M).
Local Notation S := (succM M).

Lemma good_stack_push x w p : pair_graph M x w p ->
  numerically_provable M x -> good_stack M w -> good_stack M p.
Proof.
  intros Hpair Hx Hw z h t [b [c [n [Hp [Hz Hpath]]]]] Hht.
  destruct (@Peano.zero_or_succ D (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) n) as [-> | [k ->]].
  - assert (p=z) by (eapply beta_unique; eassumption). subst z.
    destruct (pair_injective M p x w h t Hpair Hht) as [E _]. now subst h.
  - destruct (path_first M b c k p z Hp Hz Hpath) as [y [[a Hay] Hreach]].
    destruct (pair_injective M p x w a y Hpair Hay) as [_ E]. subst y.
    exact (Hw z h t Hreach Hht).
Qed.

Lemma good_stack_pop h w p : pair_graph M h w p -> good_stack M p ->
  numerically_provable M h /\ good_stack M w.
Proof.
  intros Hpair Hgood. split.
  - exact (Hgood p h w (reaches_self M p) Hpair).
  - intros z a t Hz Hat. apply (Hgood z a t); [|exact Hat].
    apply (reaches_prepend M p w z); [now exists h|exact Hz].
Qed.

Lemma tail_path_zero b c n : beta M b c O O -> tail_path M b c n ->
  beta M b c n O.
Proof.
  intros H0 Hpath.
  assert (H : forall k, coding_lt M k (S n) -> beta M b c k O).
  { apply (definable_induction M
      (fun k => coding_lt M k (S n) -> beta M b c k O)).
    - exists (Peano.sless $0 (σ $1) → beta_formula $2 $3 $0 zero),
        (n .: b .: c .: (fun _ => O)).
      intro k. rewrite holds_imp, less_formula_correct, beta_formula_correct.
      reflexivity.
    - intros _. exact H0.
    - intros k IH Hsk.
      assert (Hkn : coding_lt M k n) by (apply coding_lt_succ_cancel; exact Hsk).
      assert (Hksn : coding_lt M k (S n)) by
        (apply coding_lt_succ_cases; now left).
      destruct (beta_total M b c (S k)) as [y Hy].
      destruct (Hpath k O y Hkn (IH Hksn) Hy) as [a Ha].
      destruct (pair_at_zero M a y Ha) as [_ E]. now subst y. }
  apply H. apply coding_lt_succ.
Qed.

Lemma good_stack_zero : good_stack M O.
Proof.
  intros z h t [b [c [n [H0 [Hz Hp]]]]] Hpair.
  assert (E : z=O) by (eapply beta_unique; [exact Hz|exact (tail_path_zero b c n H0 Hp)]).
  subst z. destruct (pair_at_zero M h t Hpair) as [-> _]. apply numerical_truth.
Qed.

End Safety.
