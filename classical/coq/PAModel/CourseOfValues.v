(** Definable course-of-values induction in an arbitrary genuine PA model.
    The only induction used below is Model.definable_induction, applied to
    the ordinary PA formula for the bounded prefix of the given predicate.
    No well-foundedness of the external model order is assumed. *)
From PAModel Require Import Model FiniteCoding FiniteCRT FiniteCRTFormula.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Logic.Classical_Prop.
Unset Implicit Arguments.

(** Under the new quantifier the environment is y,x,rho. The original
    predicate expects y,rho, so only its parameter indices are shifted. *)
Definition prefix_predicate (theta : form) : form :=
  theta[($0 .: fun i => var (S (S i)))].

Definition bounded_prefix_formula (theta : form) : form :=
  ∀ (Peano.sless $0 $1 → prefix_predicate theta).

Definition bounded_prefix (M : Model) (P : carrier M -> Prop) (x : carrier M) : Prop :=
  forall y, coding_lt M y x -> P y.

Lemma prefix_predicate_correct M theta rho x y :
  holds M (y .: x .: rho) (prefix_predicate theta) <-> holds M (y .: rho) theta.
Proof.
  unfold holds,prefix_predicate. rewrite sat_comp. apply sat_ext.
  intros [|i]; reflexivity.
Qed.

Theorem bounded_prefix_formula_correct M theta rho x :
  holds M (x .: rho) (bounded_prefix_formula theta) <->
  bounded_prefix M (fun y => holds M (y .: rho) theta) x.
Proof.
  unfold bounded_prefix_formula,bounded_prefix.
  rewrite holds_forall. split; intros H y.
  - specialize (H y). rewrite holds_imp,holds_sless,prefix_predicate_correct in H.
    exact H.
  - rewrite holds_imp,holds_sless,prefix_predicate_correct. exact (H y).
Qed.

Theorem bounded_prefix_definable M P :
  Definable1 M P -> Definable1 M (bounded_prefix M P).
Proof.
  intros (theta & rho & HP).
  exists (bounded_prefix_formula theta),rho. intro x.
  rewrite bounded_prefix_formula_correct. unfold bounded_prefix.
  split; intros H y Hy.
  - exact (proj1 (HP y) (H y Hy)).
  - exact (proj2 (HP y) (H y Hy)).
Qed.

Theorem definable_strong_induction M P :
  Definable1 M P ->
  (forall x, (forall y, coding_lt M y x -> P y) -> P x) ->
  forall x, P x.
Proof.
  intros Hdef Hstep.
  assert (Hprefix : forall x, bounded_prefix M P x).
  { apply (definable_induction M (bounded_prefix M P)
      (bounded_prefix_definable M P Hdef)).
    - intros y Hy. exfalso. exact (coding_not_lt_zero M y Hy).
    - intros x IH y Hy.
      destruct (proj1 (coding_lt_succ_cases M y x) Hy) as [Hlt | Heq].
      + exact (IH y Hlt).
      + subst y. exact (Hstep x IH). }
  intro x. exact (Hstep x (Hprefix x)).
Qed.

Lemma definable_negation M P :
  Definable1 M P -> Definable1 M (fun x => ~P x).
Proof.
  intros (theta & rho & HP).
  exists (¬theta),rho. intro x.
  change (~P x <-> ~holds M (x .: rho) theta).
  rewrite HP. reflexivity.
Qed.

(** The double-negated least-number conclusion needs no classical principle. *)
Theorem definable_least_number_double_negation M P :
  Definable1 M P -> (exists x, P x) ->
  ~~(exists x, P x /\ forall y, coding_lt M y x -> ~P y).
Proof.
  intros Hdef [a Ha] Hnone.
  assert (Hnot : forall x, ~P x).
  { apply (definable_strong_induction M (fun x => ~P x)
      (definable_negation M P Hdef)).
    intros x IH Hx. apply Hnone. exists x. auto. }
  exact (Hnot a Ha).
Qed.

(** Classical logic is used only to remove the double negation of existence.
    Choice, arbitrary-predicate induction, and external well-foundedness are
    not inputs to this corollary. *)
Theorem definable_least_number M P :
  Definable1 M P -> (exists x, P x) ->
  exists x, P x /\ forall y, coding_lt M y x -> ~P y.
Proof.
  intros Hdef Hex. apply NNPP.
  exact (definable_least_number_double_negation M P Hdef Hex).
Qed.

