(** Numerical theories and their internally finite Hilbert proof predicates.
    A theory is specified by one unary ordinary PA formula. No closure of its
    axioms, truth axiom, or proof predicate is assumed. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  Pairing CodeExpressions NumericalProofs SentenceBounds.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Record NumericalTheory : Type := {
  theory_formula : form;
  theory_bounded : bounded 1 theory_formula
}.

Definition theory_axiom (M : Model) (T : NumericalTheory) (f : carrier M) : Prop :=
  holds M (f .: fun _ => zeroM M) (theory_formula T).

Definition theory_axiom_instance (T : NumericalTheory) (t : term) : form :=
  (theory_formula T)[t..].

Lemma theory_axiom_instance_correct M T rho t :
  holds M rho (theory_axiom_instance T t) <-> theory_axiom M T (evalM M rho t).
Proof.
  unfold theory_axiom_instance,theory_axiom,holds. rewrite sat_comp.
  apply (bound_ext _ (theory_bounded T)).
  intros [|i] Hi; [reflexivity|lia].
Qed.

Lemma theory_axiom_definable M T : Definable1 M (theory_axiom M T).
Proof.
  exists (theory_axiom_instance T $0),(fun _ => zeroM M).
  intro f. symmetry. apply theory_axiom_instance_correct.
Qed.

Definition theory_justified M T b c i v : Prop :=
  theory_axiom M T v \/
  (exists j k t u,
    coding_lt M j i /\ coding_lt M k i /\
    beta M b c j t /\ beta M b c k u /\ implication_graph M t v u) \/
  (exists j a h,
    coding_lt M j i /\ beta M b c j h /\ universal_graph M a h v).


Definition theory_justified_formula T (b c i v : term) : form :=
  theory_axiom_instance T v ∨
  ((∃∃∃∃
    (Peano.sless $3 (lift4 i) ∧ Peano.sless $2 (lift4 i) ∧
     beta_formula (lift4 b) (lift4 c) $3 $1 ∧
     beta_formula (lift4 b) (lift4 c) $2 $0 ∧
     implication_formula $1 (lift4 v) $0)) ∨
   (∃∃∃
    (Peano.sless $2 (lift3 i) ∧
     beta_formula (lift3 b) (lift3 c) $2 $0 ∧
     universal_formula $1 $0 (lift3 v)))).


Local Opaque holds theory_axiom_instance beta_formula implication_formula universal_formula Peano.sless.

Lemma theory_justified_formula_correct M T rho b c i v :
  holds M rho (theory_justified_formula T b c i v) <->
    theory_justified M T (evalM M rho b) (evalM M rho c) (evalM M rho i) (evalM M rho v).
Proof.
  unfold theory_justified_formula, theory_justified.
  repeat setoid_rewrite holds_or.
  repeat setoid_rewrite holds_ex.
  repeat setoid_rewrite holds_and.
  rewrite theory_axiom_instance_correct.
  setoid_rewrite less_formula_correct.
  setoid_rewrite beta_formula_correct.
  setoid_rewrite implication_formula_correct.
  setoid_rewrite universal_formula_correct.
  setoid_rewrite lift4_correct.
  setoid_rewrite lift3_correct.
  split; intros [Ha | [Hmp | Hg]].
  - now left.
  - right; left. destruct Hmp as [j [k [t [u H]]]]. exists j,k,t,u. tauto.
  - right; right. destruct Hg as [j [a [h H]]]. exists j,a,h. tauto.
  - now left.
  - right; left. destruct Hmp as [j [k [t [u H]]]]. exists j,k,t,u. tauto.
  - right; right. destruct Hg as [j [a [h H]]]. exists j,a,h. tauto.
Qed.

Local Opaque theory_justified_formula.

Definition theory_proof_sequence M T b c n : Prop :=
  forall i v, coding_lt M i n -> beta M b c i v -> theory_justified M T b c i v.

Definition theory_proof_sequence_formula T (b c n : term) : form :=
  ∀∀ (Peano.sless $1 (code_lift2 n) →
    beta_formula (code_lift2 b) (code_lift2 c) $1 $0 →
    theory_justified_formula T (code_lift2 b) (code_lift2 c) $1 $0).

Lemma theory_proof_sequence_formula_correct M T rho b c n :
  holds M rho (theory_proof_sequence_formula T b c n) <->
    theory_proof_sequence M T (evalM M rho b) (evalM M rho c) (evalM M rho n).
Proof.
  unfold theory_proof_sequence_formula, theory_proof_sequence.
  repeat setoid_rewrite holds_all.
  repeat setoid_rewrite holds_imp.
  setoid_rewrite less_formula_correct.
  setoid_rewrite beta_formula_correct.
  setoid_rewrite theory_justified_formula_correct.
  setoid_rewrite code_eval_lift2.
  reflexivity.
Qed.

Definition theory_derivation M T b c n f : Prop :=
  theory_proof_sequence M T b c (succM M n) /\ beta M b c n f.

Definition theory_derivation_formula T (b c n f : term) : form :=
  theory_proof_sequence_formula T b c (σ n) ∧ beta_formula b c n f.

Lemma theory_derivation_formula_correct M T rho b c n f :
  holds M rho (theory_derivation_formula T b c n f) <->
    theory_derivation M T (evalM M rho b) (evalM M rho c)
      (evalM M rho n) (evalM M rho f).
Proof.
  unfold theory_derivation_formula, theory_derivation.
  rewrite holds_and.
  rewrite theory_proof_sequence_formula_correct, beta_formula_correct. reflexivity.
Qed.

Definition theory_provable M T f : Prop :=
  exists b c n, theory_derivation M T b c n f.

Definition theory_provable_formula T (f : term) : form :=
  ∃∃∃ theory_derivation_formula T $2 $1 $0 (lift3 f).

Lemma theory_provable_formula_correct M T rho f :
  holds M rho (theory_provable_formula T f) <->
    theory_provable M T (evalM M rho f).
Proof.
  unfold theory_provable_formula, theory_provable.
  repeat setoid_rewrite holds_ex.
  setoid_rewrite theory_derivation_formula_correct.
  setoid_rewrite lift3_correct. reflexivity.
Qed.

Lemma theory_provable_definable M T : Definable1 M (theory_provable M T).
Proof. exists (theory_provable_formula T $0), (fun _ => zeroM M).
  intro f. symmetry. apply theory_provable_formula_correct. Qed.

(** The original concrete proof predicate is recovered without changing its
    numerical axiom codes, beta representation, or inference rules. *)
Lemma K230_axiom_unary : bounded 1 (K230_axiom_formula $0).
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

Definition K230Theory : NumericalTheory :=
  {| theory_formula := K230_axiom_formula $0;
     theory_bounded := K230_axiom_unary |}.

Lemma K230Theory_axiom M f :
  theory_axiom M K230Theory f <-> K230_axiom_relation M f.
Proof. unfold theory_axiom,K230Theory. apply K230_axiom_formula_correct. Qed.

Lemma K230Theory_justified M b c i v :
  theory_justified M K230Theory b c i v <-> justified M b c i v.
Proof. unfold theory_justified,justified. rewrite K230Theory_axiom. reflexivity. Qed.

Lemma K230Theory_proof_sequence M b c n :
  theory_proof_sequence M K230Theory b c n <-> proof_sequence M b c n.
Proof. unfold theory_proof_sequence,proof_sequence.
  setoid_rewrite K230Theory_justified. reflexivity. Qed.

Lemma K230Theory_derivation M b c n f :
  theory_derivation M K230Theory b c n f <-> numerical_derivation M b c n f.
Proof. unfold theory_derivation,numerical_derivation.
  rewrite K230Theory_proof_sequence. reflexivity. Qed.

Theorem K230Theory_provable M f :
  theory_provable M K230Theory f <-> numerically_provable M f.
Proof. unfold theory_provable,numerically_provable.
  setoid_rewrite K230Theory_derivation. reflexivity. Qed.
