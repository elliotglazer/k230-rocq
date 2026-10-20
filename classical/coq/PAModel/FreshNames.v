(** All variable names in internally reachable nodes are below the original
    named-formula code. Paths have model-valued lengths and are beta-coded.
    This concerns the raw four-tag syntax, including Wel(0,0) at code 1.
    It does not identify that syntax with a full ZFC source language. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  FiniteCRTFormula Pairing CodeExpressions NumericalProofs ProofClosure
  CodeDescent CodeTags.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Definition formula_edge M (f g : carrier M) : Prop :=
  exists a b,
    (f <> zeroM M /\ tagged_pair_graph M 0 a b f /\ (g=a \/ g=b)) \/
    (tagged_pair_graph M 2 a b f /\ g=b).

Definition formula_edge_formula (f g : term) : form :=
  ∃∃ (((¬ (code_lift2 f == zero)) ∧
         (tagged_pair_formula 0 $1 $0 (code_lift2 f) ∧
          ((code_lift2 g == $1) ∨ (code_lift2 g == $0)))) ∨
       (tagged_pair_formula 2 $1 $0 (code_lift2 f) ∧ (code_lift2 g == $0))).

Lemma fresh_holds_eq M rho a b : holds M rho (a == b) <->
  evalM M rho a = evalM M rho b.
Proof. reflexivity. Qed.

Local Opaque holds tagged_pair_formula.

Lemma formula_edge_formula_correct M rho f g :
  holds M rho (formula_edge_formula f g) <->
  formula_edge M (evalM M rho f) (evalM M rho g).
Proof.
  unfold formula_edge_formula, formula_edge.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_or.
  repeat setoid_rewrite holds_and. repeat setoid_rewrite holds_or.
  setoid_rewrite code_holds_neq.
  setoid_rewrite tagged_pair_formula_correct.
  setoid_rewrite fresh_holds_eq.
  setoid_rewrite code_eval_lift2.
  reflexivity.
Qed.

Lemma formula_edge_decreases M f g :
  formula_edge M f g -> coding_lt M g f.
Proof.
  intros [a [b [H|H]]].
  - destruct H as [Hnz [H [E|E]]]; subst g.
    + exact (proj1 (tagged_pair_zero_descent M a b f Hnz H)).
    + exact (proj2 (tagged_pair_zero_descent M a b f Hnz H)).
  - destruct H as [H E]. subst g.
    exact (proj2 (tagged_pair_positive_descent M a b f 2 ltac:(lia) H)).
Qed.

Definition formula_path M (b c n : carrier M) : Prop :=
  forall i x y, coding_lt M i n -> beta M b c i x ->
    beta M b c (succM M i) y -> formula_edge M x y.
Definition formula_reaches M (f g : carrier M) : Prop :=
  exists b c n, beta M b c (zeroM M) f /\ beta M b c n g /\ formula_path M b c n.

Definition formula_path_formula (b c n : term) : form :=
  ∀∀∀ (Peano.sless $2 (lift3 n) →
    beta_formula (lift3 b) (lift3 c) $2 $1 →
    beta_formula (lift3 b) (lift3 c) (σ $2) $0 →
    formula_edge_formula $1 $0).
Definition formula_reaches_formula (f g : term) : form :=
  ∃∃∃ (beta_formula $2 $1 zero (lift3 f) ∧
    (beta_formula $2 $1 $0 (lift3 g) ∧ formula_path_formula $2 $1 $0)).

Local Opaque beta_formula Peano.sless formula_edge_formula.

Lemma formula_path_formula_correct M rho b c n :
  holds M rho (formula_path_formula b c n) <->
  formula_path M (evalM M rho b) (evalM M rho c) (evalM M rho n).
Proof.
  unfold formula_path_formula, formula_path.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite less_formula_correct. setoid_rewrite beta_formula_correct.
  setoid_rewrite formula_edge_formula_correct.
  setoid_rewrite lift3_correct. reflexivity.
Qed.

Local Opaque formula_path_formula.

Lemma formula_reaches_formula_correct M rho f g :
  holds M rho (formula_reaches_formula f g) <->
  formula_reaches M (evalM M rho f) (evalM M rho g).
Proof.
  unfold formula_reaches_formula, formula_reaches.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite beta_formula_correct. setoid_rewrite formula_path_formula_correct.
  setoid_rewrite lift3_correct. reflexivity.
Qed.

Definition node_mentions M (f v : carrier M) : Prop :=
  exists a b,
    ((tagged_pair_graph M 1 a b f \/ tagged_pair_graph M 3 a b f) /\ (v=a \/ v=b)) \/
    (tagged_pair_graph M 2 a b f /\ v=a).
Definition node_mentions_formula (f v : term) : form :=
  ∃∃ (((tagged_pair_formula 1 $1 $0 (code_lift2 f) ∨
          tagged_pair_formula 3 $1 $0 (code_lift2 f)) ∧
         ((code_lift2 v == $1) ∨ (code_lift2 v == $0))) ∨
       (tagged_pair_formula 2 $1 $0 (code_lift2 f) ∧ (code_lift2 v == $1))).

Lemma node_mentions_formula_correct M rho f v :
  holds M rho (node_mentions_formula f v) <->
  node_mentions M (evalM M rho f) (evalM M rho v).
Proof.
  unfold node_mentions_formula, node_mentions.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_or.
  repeat setoid_rewrite holds_and. repeat setoid_rewrite holds_or.
  setoid_rewrite tagged_pair_formula_correct. setoid_rewrite fresh_holds_eq.
  setoid_rewrite code_eval_lift2. reflexivity.
Qed.

Lemma node_mentions_bounded M f v : node_mentions M f v -> coding_lt M v f.
Proof.
  intros [a [b [H|H]]].
  - destruct H as [[H|H] [E|E]]; subst v.
    + exact (proj1 (tagged_pair_positive_descent M a b f 1 ltac:(lia) H)).
    + exact (proj2 (tagged_pair_positive_descent M a b f 1 ltac:(lia) H)).
    + exact (proj1 (tagged_pair_positive_descent M a b f 3 ltac:(lia) H)).
    + exact (proj2 (tagged_pair_positive_descent M a b f 3 ltac:(lia) H)).
  - destruct H as [H E]. subst v.
    exact (proj1 (tagged_pair_positive_descent M a b f 2 ltac:(lia) H)).
Qed.

Definition formula_mentions M (f v : carrier M) : Prop :=
  exists g, formula_reaches M f g /\ node_mentions M g v.
Definition formula_mentions_formula (f v : term) : form :=
  ∃ (formula_reaches_formula f`[↑] $0 ∧ node_mentions_formula $0 v`[↑]).

Local Opaque formula_reaches_formula node_mentions_formula.

Lemma formula_mentions_formula_correct M rho f v :
  holds M rho (formula_mentions_formula f v) <->
  formula_mentions M (evalM M rho f) (evalM M rho v).
Proof.
  unfold formula_mentions_formula, formula_mentions.
  rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite formula_reaches_formula_correct.
  setoid_rewrite node_mentions_formula_correct.
  unfold evalM. setoid_rewrite eval_up. reflexivity.
Qed.

Lemma formula_mentions_definable M f : Definable1 M (formula_mentions M f).
Proof.
  exists (formula_mentions_formula $1 $0), (f .: (fun _ => zeroM M)).
  intro v. symmetry. apply formula_mentions_formula_correct.
Qed.

Section Bounds.
Variable M : Model.
Local Notation D := (carrier M).
Local Notation O := (zeroM M).
Local Notation S := (succM M).

Lemma formula_reaches_self f : formula_reaches M f f.
Proof.
  exists f,f,O. split; [apply beta_singleton|].
  split; [apply beta_singleton|].
  intros i x y Hi. exfalso. exact (coding_not_lt_zero M i Hi).
Qed.

Theorem formula_path_bounded b c n f :
  beta M b c O f -> formula_path M b c n ->
  forall k g, coding_lt M k (S n) -> beta M b c k g ->
    g=f \/ coding_lt M g f.
Proof.
  intros Hzero Hpath.
  assert (HI : forall k, coding_lt M k (S n) ->
      forall g, beta M b c k g -> g=f \/ coding_lt M g f).
  { apply (definable_induction M (fun k => coding_lt M k (S n) ->
        forall g, beta M b c k g -> g=f \/ coding_lt M g f)).
    - exists (Peano.sless $0 (σ $1) →
        ∀ (beta_formula $3 $4 $1 $0 → (($0 == $5) ∨ Peano.sless $0 $5))),
        (n .: b .: c .: f .: (fun _ => O)).
      intro k. repeat setoid_rewrite holds_imp. setoid_rewrite holds_all.
      repeat setoid_rewrite holds_imp. setoid_rewrite holds_or.
      setoid_rewrite less_formula_correct. setoid_rewrite beta_formula_correct.
      setoid_rewrite fresh_holds_eq.
      reflexivity.
    - intros _ g Hg. left. exact (beta_unique M b c O g f Hg Hzero).
    - intros k IH Hsk g Hg.
      assert (Hkn : coding_lt M k n) by (apply coding_lt_succ_cancel; exact Hsk).
      assert (Hksn : coding_lt M k (S n)) by (apply coding_lt_succ_cases; now left).
      destruct (beta_total M b c k) as [h Hh].
      pose proof (formula_edge_decreases M h g (Hpath k h g Hkn Hh Hg)) as Hgh.
      right. destruct (IH Hksn h Hh) as [->|Hhf]; [exact Hgh|].
      exact (coding_lt_trans M g h f Hgh Hhf). }
  intros k g Hk Hg. exact (HI k Hk g Hg).
Qed.

Corollary formula_reaches_bounded f g :
  formula_reaches M f g -> g=f \/ coding_lt M g f.
Proof.
  intros [b [c [n [Hf [Hg Hp]]]]].
  exact (formula_path_bounded b c n f Hf Hp n g (coding_lt_succ M n) Hg).
Qed.

Theorem formula_mentions_bounded f v :
  formula_mentions M f v -> coding_lt M v f.
Proof.
  intros [g [Hreach Hmention]].
  pose proof (node_mentions_bounded M g v Hmention) as Hvg.
  destruct (formula_reaches_bounded f g Hreach) as [->|Hgf]; [exact Hvg|].
  exact (coding_lt_trans M v g f Hvg Hgf).
Qed.

Definition formula_fresh (f k : D) : Prop :=
  forall v, formula_mentions M f v -> v<>k.

Theorem formula_code_is_fresh f : formula_fresh f f.
Proof.
  intros v Hv. exact (@Peano.lt_neq D (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) v f (formula_mentions_bounded f v Hv)).
Qed.

Theorem formula_above_is_fresh f k : coding_lt M f k -> formula_fresh f k.
Proof.
  intros Hfk v Hv. exact (@Peano.lt_neq D (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) v k
    (coding_lt_trans M v f k (formula_mentions_bounded f v Hv) Hfk)).
Qed.

Corollary formula_successor_is_fresh f : formula_fresh f (S f).
Proof. apply formula_above_is_fresh, coding_lt_succ. Qed.

End Bounds.

Definition formula_fresh_formula (f k : term) : form :=
  ∀ (formula_mentions_formula f`[↑] $0 → ¬ ($0 == k`[↑])).

Local Opaque formula_mentions_formula.

Theorem formula_fresh_formula_correct M rho f k :
  holds M rho (formula_fresh_formula f k) <->
  formula_fresh M (evalM M rho f) (evalM M rho k).
Proof.
  unfold formula_fresh_formula, formula_fresh.
  rewrite holds_all. setoid_rewrite holds_imp.
  setoid_rewrite formula_mentions_formula_correct.
  setoid_rewrite code_holds_neq.
  unfold evalM. setoid_rewrite eval_up. reflexivity.
Qed.

Theorem fresh_bound_sentence_true M rho :
  holds M rho (∀∀ (Peano.sless $1 $0 → formula_fresh_formula $1 $0)).
Proof.
  rewrite holds_all. intro f. rewrite holds_all. intro k.
  rewrite holds_imp, less_formula_correct, formula_fresh_formula_correct.
  exact (formula_above_is_fresh M f k).
Qed.
