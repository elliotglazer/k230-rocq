(** A numerical Hilbert proof predicate. All proof lengths, line numbers,
    formulas and witnesses are elements of the arbitrary PA model. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  Pairing CodeExpressions.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Definition arguments2 {A : Type} (a b d : A) : nat -> A :=
  fun i => match i with 0 => a | 1 => b | _ => d end.

Lemma holds_or M rho p q :
  holds M rho (p ∨ q) <-> (holds M rho p \/ holds M rho q).
Proof. reflexivity. Qed.
Lemma holds_and M rho p q :
  holds M rho (p ∧ q) <-> (holds M rho p /\ holds M rho q).
Proof. reflexivity. Qed.
Lemma holds_imp M rho p q :
  holds M rho (p → q) <-> (holds M rho p -> holds M rho q).
Proof. reflexivity. Qed.
Lemma holds_all M rho p :
  holds M rho (∀ p) <-> (forall x, holds M (x .: rho) p).
Proof. reflexivity. Qed.
Lemma holds_ex M rho p :
  holds M rho (∃ p) <-> (exists x, holds M (x .: rho) p).
Proof. reflexivity. Qed.

Definition implication_graph M a b z :=
  code_relation M (arguments2 a b (zeroM M))
    (E_wim (CEvar 0) (CEvar 1)) z.
Definition universal_graph M a b z :=
  code_relation M (arguments2 a b (zeroM M))
    (E_wal (CEvar 0) (CEvar 1)) z.

Definition implication_formula (a b z : term) :=
  code_formula (E_wim (CEvar 0) (CEvar 1)) (arguments2 a b zero) z.
Definition universal_formula (a b z : term) :=
  code_formula (E_wal (CEvar 0) (CEvar 1)) (arguments2 a b zero) z.

Lemma implication_formula_correct M rho a b z :
  holds M rho (implication_formula a b z) <->
    implication_graph M (evalM M rho a) (evalM M rho b) (evalM M rho z).
Proof. unfold implication_formula, implication_graph. rewrite code_formula_correct.
  apply code_relation_ext. intros [|[|i]]; reflexivity. Qed.
Lemma universal_formula_correct M rho a b z :
  holds M rho (universal_formula a b z) <->
    universal_graph M (evalM M rho a) (evalM M rho b) (evalM M rho z).
Proof. unfold universal_formula, universal_graph. rewrite code_formula_correct.
  apply code_relation_ext. intros [|[|i]]; reflexivity. Qed.

Definition justified M b c i v : Prop :=
  K230_axiom_relation M v \/
  (exists j k t u,
    coding_lt M j i /\ coding_lt M k i /\
    beta M b c j t /\ beta M b c k u /\ implication_graph M t v u) \/
  (exists j a h,
    coding_lt M j i /\ beta M b c j h /\ universal_graph M a h v).

Definition lift3 (t : term) := t`[↑]`[↑]`[↑].
Definition lift4 (t : term) := t`[↑]`[↑]`[↑]`[↑].

Definition justified_formula (b c i v : term) : form :=
  K230_axiom_formula v ∨
  ((∃∃∃∃
    (Peano.sless $3 (lift4 i) ∧ Peano.sless $2 (lift4 i) ∧
     beta_formula (lift4 b) (lift4 c) $3 $1 ∧
     beta_formula (lift4 b) (lift4 c) $2 $0 ∧
     implication_formula $1 (lift4 v) $0)) ∨
   (∃∃∃
    (Peano.sless $2 (lift3 i) ∧
     beta_formula (lift3 b) (lift3 c) $2 $0 ∧
     universal_formula $1 $0 (lift3 v)))).

Lemma lift3_correct M rho a b c t :
  evalM M (c .: b .: a .: rho) (lift3 t) = evalM M rho t.
Proof. unfold evalM, lift3. now rewrite !eval_up. Qed.
Lemma lift4_correct M rho a b c d t :
  evalM M (d .: c .: b .: a .: rho) (lift4 t) = evalM M rho t.
Proof. unfold evalM, lift4. now rewrite !eval_up. Qed.

Lemma less_formula_correct M rho a b :
  holds M rho (Peano.sless a b) <-> coding_lt M (evalM M rho a) (evalM M rho b).
Proof. unfold holds, Peano.sless, coding_lt, evalM. cbn.
  split; intros [d H]; exists d.
  - rewrite !(@eval_up _ _ (carrier M) (interpretation M) rho d) in H. exact H.
  - rewrite !(@eval_up _ _ (carrier M) (interpretation M) rho d). exact H.
Qed.

Local Opaque holds K230_axiom_formula beta_formula implication_formula universal_formula Peano.sless.

Lemma justified_formula_correct M rho b c i v :
  holds M rho (justified_formula b c i v) <->
    justified M (evalM M rho b) (evalM M rho c) (evalM M rho i) (evalM M rho v).
Proof.
  unfold justified_formula, justified.
  repeat setoid_rewrite holds_or.
  repeat setoid_rewrite holds_ex.
  repeat setoid_rewrite holds_and.
  rewrite K230_axiom_formula_correct.
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

Local Opaque justified_formula.

Definition proof_sequence M b c n : Prop :=
  forall i v, coding_lt M i n -> beta M b c i v -> justified M b c i v.

Definition proof_sequence_formula (b c n : term) : form :=
  ∀∀ (Peano.sless $1 (code_lift2 n) →
    beta_formula (code_lift2 b) (code_lift2 c) $1 $0 →
    justified_formula (code_lift2 b) (code_lift2 c) $1 $0).

Lemma proof_sequence_formula_correct M rho b c n :
  holds M rho (proof_sequence_formula b c n) <->
    proof_sequence M (evalM M rho b) (evalM M rho c) (evalM M rho n).
Proof.
  unfold proof_sequence_formula, proof_sequence.
  repeat setoid_rewrite holds_all.
  repeat setoid_rewrite holds_imp.
  setoid_rewrite less_formula_correct.
  setoid_rewrite beta_formula_correct.
  setoid_rewrite justified_formula_correct.
  setoid_rewrite code_eval_lift2.
  reflexivity.
Qed.

Definition numerical_derivation M b c n f : Prop :=
  proof_sequence M b c (succM M n) /\ beta M b c n f.

Definition numerical_derivation_formula (b c n f : term) : form :=
  proof_sequence_formula b c (σ n) ∧ beta_formula b c n f.

Lemma numerical_derivation_formula_correct M rho b c n f :
  holds M rho (numerical_derivation_formula b c n f) <->
    numerical_derivation M (evalM M rho b) (evalM M rho c)
      (evalM M rho n) (evalM M rho f).
Proof.
  unfold numerical_derivation_formula, numerical_derivation.
  rewrite holds_and.
  rewrite proof_sequence_formula_correct, beta_formula_correct. reflexivity.
Qed.

Definition numerically_provable M f : Prop :=
  exists b c n, numerical_derivation M b c n f.

Definition numerically_provable_formula (f : term) : form :=
  ∃∃∃ numerical_derivation_formula $2 $1 $0 (lift3 f).

Lemma numerically_provable_formula_correct M rho f :
  holds M rho (numerically_provable_formula f) <->
    numerically_provable M (evalM M rho f).
Proof.
  unfold numerically_provable_formula, numerically_provable.
  repeat setoid_rewrite holds_ex.
  setoid_rewrite numerical_derivation_formula_correct.
  setoid_rewrite lift3_correct. reflexivity.
Qed.

Lemma numerically_provable_definable M : Definable1 M (numerically_provable M).
Proof. exists (numerically_provable_formula $0), (fun _ => zeroM M).
  intro f. symmetry. apply numerically_provable_formula_correct. Qed.
