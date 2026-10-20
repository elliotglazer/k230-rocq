(** Induction over internally finite Hilbert proofs. The predicate on proof
    lines must be definable by an ordinary PA formula. All proof lengths and
    line indices belong to the arbitrary model, not to Rocq's nat. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  CodeExpressions NumericalProofs NumericalTheories TheoryProofClosure
  CourseOfValues.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Definition proof_line_predicate (theta : form) : form :=
  theta[($0 .: fun i => var (5+i))].

Definition proof_line_property (theta : form) : form :=
  Peano.sless $0 (σ $3) →
    ∀ (beta_formula $2 $3 $1 $0 → proof_line_predicate theta).

Lemma proof_line_predicate_correct M theta rho b c n i v :
  holds M (v .: i .: b .: c .: n .: rho) (proof_line_predicate theta) <->
  holds M (v .: rho) theta.
Proof.
  unfold holds,proof_line_predicate. rewrite sat_comp. apply sat_ext.
  intros [|j]; reflexivity.
Qed.

Lemma proof_line_property_correct M theta rho b c n i :
  holds M (i .: b .: c .: n .: rho) (proof_line_property theta) <->
  (coding_lt M i (succM M n) -> forall v,
    beta M b c i v -> holds M (v .: rho) theta).
Proof.
  unfold proof_line_property. rewrite holds_imp,less_formula_correct.
  setoid_rewrite holds_all. setoid_rewrite holds_imp.
  setoid_rewrite beta_formula_correct.
  setoid_rewrite proof_line_predicate_correct. reflexivity.
Qed.

Lemma proof_line_property_definable M P b c n :
  Definable1 M P -> Definable1 M (fun i =>
    coding_lt M i (succM M n) -> forall v, beta M b c i v -> P v).
Proof.
  intros [theta [rho HP]].
  exists (proof_line_property theta),(b .: c .: n .: rho).
  intro i. rewrite proof_line_property_correct.
  split; intros H Hi v Hv.
  - exact (proj1 (HP v) (H Hi v Hv)).
  - exact (proj2 (HP v) (H Hi v Hv)).
Qed.

Theorem theory_proof_induction M T P :
  Definable1 M P ->
  (forall f, theory_axiom M T f -> P f) ->
  (forall a b h, P a -> P h -> implication_graph M a b h -> P b) ->
  (forall a h f, P h -> universal_graph M a h f -> P f) ->
  forall f, theory_provable M T f -> P f.
Proof.
  intros Hdef Hax Hmp Hgen f [b [c [n [Hseq Hfinal]]]].
  assert (Hall : forall i, coding_lt M i (succM M n) ->
      forall v, beta M b c i v -> P v).
  { apply (definable_strong_induction M
      (fun i => coding_lt M i (succM M n) ->
        forall v, beta M b c i v -> P v)
      (proof_line_property_definable M P b c n Hdef)).
    intros i IH Hi v Hv.
    destruct (Hseq i v Hi Hv) as [Ha|[Hdetach|Hgeneralize]].
    - exact (Hax v Ha).
    - destruct Hdetach as [j [k [a [h [Hj [Hk [Hja [Hkh Himp]]]]]]]].
      apply (Hmp a v h).
      + exact (IH j Hj (coding_lt_trans M j i (succM M n) Hj Hi) a Hja).
      + exact (IH k Hk (coding_lt_trans M k i (succM M n) Hk Hi) h Hkh).
      + exact Himp.
    - destruct Hgeneralize as [j [a [h [Hj [Hjh Hall]]]]].
      apply (Hgen a h v).
      + exact (IH j Hj (coding_lt_trans M j i (succM M n) Hj Hi) h Hjh).
      + exact Hall. }
  exact (Hall n (coding_lt_succ M n) f Hfinal).
Qed.

(** This theorem does not iterate in Rocq over a nonstandard proof. It
    applies PA induction to target provability, which is an explicit formula. *)
Theorem theory_provable_monotone M S T :
  (forall f, theory_axiom M S f -> theory_provable M T f) ->
  forall f, theory_provable M S f -> theory_provable M T f.
Proof.
  intro Hax. apply (theory_proof_induction M S (theory_provable M T)).
  - apply theory_provable_definable.
  - exact Hax.
  - exact (theory_numerical_mp M T).
  - exact (theory_numerical_gen M T).
Qed.

Definition theory_consistent M T :=
  ~theory_provable M T (code_numeral M 1).

Corollary theory_consistency_antitone M S T :
  (forall f, theory_axiom M S f -> theory_provable M T f) ->
  theory_consistent M T -> theory_consistent M S.
Proof.
  intros Hax HC HS. apply HC.
  exact (theory_provable_monotone M S T Hax (code_numeral M 1) HS).
Qed.

Corollary theory_equiconsistency_from_mutual_axiom_proofs M S T :
  (forall f, theory_axiom M S f -> theory_provable M T f) ->
  (forall f, theory_axiom M T f -> theory_provable M S f) ->
  (theory_consistent M S <-> theory_consistent M T).
Proof.
  intros HST HTS. split.
  - exact (theory_consistency_antitone M T S HTS).
  - exact (theory_consistency_antitone M S T HST).
Qed.

Print Assumptions theory_proof_induction.
Print Assumptions theory_provable_monotone.
Print Assumptions theory_equiconsistency_from_mutual_axiom_proofs.
