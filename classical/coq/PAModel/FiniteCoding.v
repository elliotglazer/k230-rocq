(** A first arithmetic coding layer over genuine PA models.

    This file proves totality and uniqueness of Goedel beta READING, including
    at nonstandard indices. It does not yet prove that arbitrary finite
    sequences can be packed, or closure of proof certificates under append.

    Arithmetic input: FOL.Tennenbaum.Peano.iEuclid and iFac_unique, from
    coq-library-fol commit 4e5702240aa0cae803dbb2d4bc5a4b7744fef217.
    Those lemmas derive their results from the ordinary PA induction schema.
    No CT/CTQ, arithmetic soundness axiom, or sequence-coding axiom is used. *)
From PAModel Require Import Model.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Import Vector.VectorNotations.
Unset Implicit Arguments.

Definition coding_lt (M : Model) (x y : carrier M) : Prop :=
  exists d, y = succM M (addM M x d).

Definition remainder (M : Model) (x q r : carrier M) : Prop :=
  coding_lt M r q /\ exists d, x = addM M (mulM M d q) r.

Definition beta_modulus (M : Model) (c i : carrier M) : carrier M :=
  succM M (mulM M (succM M i) c).

Definition beta (M : Model) (b c i r : carrier M) : Prop :=
  remainder M b (beta_modulus M c i) r.

Lemma coding_add_comm (M : Model) (x y : carrier M) :
  addM M x y = addM M y x.
Proof.
  exact (@Peano.add_comm (carrier M) (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) x y).
Qed.

Lemma coding_add_zero (M : Model) (x : carrier M) :
  addM M (zeroM M) x = x.
Proof.
  exact (@Peano.add_zero (carrier M) (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) x).
Qed.

Lemma coding_add_zero_r (M : Model) (x : carrier M) :
  addM M x (zeroM M) = x.
Proof. rewrite coding_add_comm. apply coding_add_zero. Qed.

Lemma coding_mul_zero (M : Model) (x : carrier M) :
  mulM M (zeroM M) x = zeroM M.
Proof.
  exact (@Peano.mult_zero (carrier M) (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) x).
Qed.

Lemma coding_mul_one (M : Model) (x : carrier M) :
  mulM M (succM M (zeroM M)) x = x.
Proof.
  pose proof (@Peano.mult_rec (carrier M) (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) x (zeroM M)) as Hrec.
  change (mulM M (succM M (zeroM M)) x =
    addM M x (mulM M (zeroM M) x)) in Hrec.
  rewrite Hrec.
  rewrite coding_mul_zero. apply coding_add_zero_r.
Qed.

Lemma coding_lt_succ (M : Model) (x : carrier M) :
  coding_lt M x (succM M x).
Proof. exists (zeroM M). now rewrite coding_add_zero_r. Qed.

Lemma coding_zero_lt_succ (M : Model) (x : carrier M) :
  coding_lt M (zeroM M) (succM M x).
Proof. exists x. now rewrite coding_add_zero. Qed.

Lemma remainder_total (M : Model) (x q : carrier M) :
  coding_lt M (zeroM M) q -> exists r, remainder M x q r.
Proof.
  intros Hq.
  destruct (@Peano.iEuclid (carrier M) (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) x q) as [d [r [He Hr]]].
  exists r. split; [exact (Hr Hq)|now exists d].
Qed.

Lemma remainder_unique (M : Model) (x q r s : carrier M) :
  remainder M x q r -> remainder M x q s -> r = s.
Proof.
  intros [Hr [d Hd]] [Hs [e He]].
  assert (Hde : addM M r (mulM M d q) = addM M s (mulM M e q)).
  { rewrite (coding_add_comm M r), (coding_add_comm M s).
    now rewrite <- Hd, <- He. }
  exact (proj2 (@Peano.iFac_unique (carrier M) (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) q d r e s Hr Hs Hde)).
Qed.

Lemma beta_total (M : Model) (b c i : carrier M) :
  exists r, beta M b c i r.
Proof.
  apply remainder_total. apply coding_zero_lt_succ.
Qed.

Lemma beta_unique (M : Model) (b c i r s : carrier M) :
  beta M b c i r -> beta M b c i s -> r = s.
Proof. apply remainder_unique. Qed.

Lemma beta_zero (M : Model) (c i : carrier M) :
  beta M (zeroM M) c i (zeroM M).
Proof.
  split; [apply coding_zero_lt_succ|].
  exists (zeroM M). rewrite coding_mul_zero, coding_add_zero. reflexivity.
Qed.

Lemma beta_singleton (M : Model) (x : carrier M) :
  beta M x x (zeroM M) x.
Proof.
  unfold beta, beta_modulus. rewrite coding_mul_one.
  split; [apply coding_lt_succ|].
  exists (zeroM M). rewrite coding_mul_zero, coding_add_zero. reflexivity.
Qed.

(** These are ordinary PA formulas, with no new predicate or function symbol. *)
Definition remainder_formula (x q r : term) : form :=
  Peano.sless r q ∧ (∃ x`[↑] == ($0 ⊗ q`[↑]) ⊕ r`[↑]).

Definition beta_formula (b c i r : term) : form :=
  remainder_formula b (σ ((σ i) ⊗ c)) r.

Definition evalM (M : Model) (rho : nat -> carrier M) (t : term) : carrier M :=
  @eval _ _ (carrier M) (interpretation M) rho t.

Lemma remainder_formula_correct (M : Model) (rho : nat -> carrier M)
    (x q r : term) :
  holds M rho (remainder_formula x q r) <->
  remainder M (evalM M rho x) (evalM M rho q) (evalM M rho r).
Proof.
  unfold holds, remainder_formula, Peano.sless, remainder, coding_lt, evalM.
  cbn.
  split.
  - intros [[d Hd] [e He]]. split.
    + exists d. rewrite !(@eval_up _ _ (carrier M) (interpretation M) rho d) in Hd.
      exact Hd.
    + exists e. rewrite !(@eval_up _ _ (carrier M) (interpretation M) rho e) in He.
      exact He.
  - intros [[d Hd] [e He]]. split.
    + exists d. rewrite !(@eval_up _ _ (carrier M) (interpretation M) rho d).
      exact Hd.
    + exists e. rewrite !(@eval_up _ _ (carrier M) (interpretation M) rho e).
      exact He.
Qed.

Lemma beta_formula_correct (M : Model) (rho : nat -> carrier M)
    (b c i r : term) :
  holds M rho (beta_formula b c i r) <->
  beta M (evalM M rho b) (evalM M rho c) (evalM M rho i) (evalM M rho r).
Proof.
  unfold beta_formula. rewrite remainder_formula_correct. reflexivity.
Qed.

Definition beta4 : form := beta_formula $3 $2 $1 $0.

Lemma beta4_correct (M : Model) (rho : nat -> carrier M)
    (b c i r : carrier M) :
  holds M (r .: i .: c .: b .: rho) beta4 <-> beta M b c i r.
Proof. apply beta_formula_correct. Qed.

Lemma beta_value_definable (M : Model) (b c i : carrier M) :
  Definable1 M (fun r => beta M b c i r).
Proof.
  exists beta4, (i .: c .: b .: (fun _ => zeroM M)).
  intro r. symmetry. apply beta4_correct.
Qed.

Lemma beta_index_definable (M : Model) (b c r : carrier M) :
  Definable1 M (fun i => beta M b c i r).
Proof.
  exists (beta_formula $3 $2 $0 $1), (r .: c .: b .: (fun _ => zeroM M)).
  intro i. symmetry. apply beta_formula_correct.
Qed.

Lemma beta4_bounded : bounded 4 beta4.
Proof.
  unfold beta4, beta_formula, remainder_formula, Peano.sless.
  repeat solve_bounds.
Qed.

Definition beta_total_sentence : form := ∀∀∀∃ beta4.

Lemma beta_total_sentence_valid (M : Model) (rho : nat -> carrier M) :
  holds M rho beta_total_sentence.
Proof.
  change (forall b c i : carrier M,
    exists r : carrier M, holds M (r .: i .: c .: b .: rho) beta4).
  intros b c i. destruct (beta_total M b c i) as [r Hr].
  exists r. apply (proj2 (beta4_correct M rho b c i r)). exact Hr.
Qed.

(* The following arithmetic construction is the first ingredient for beta
   repacking.  The bound n is an arbitrary element of the PA model; this is
   not induction over an external Rocq natural number. *)
Definition positive_common_multiple (M : Model) (n m : carrier M) : Prop :=
  coding_lt M (zeroM M) m /\
  forall d, (coding_lt M (zeroM M) d /\ coding_lt M d (succM M n)) ->
    exists k, m = mulM M d k.

Definition common_multiple_formula : form :=
  ∃ (Peano.sless zero $0 ∧
    ∀ ((Peano.sless zero $0 ∧ Peano.sless $0 (σ $2)) →
      ∃ $2 == ($1 ⊗ $0))).

Lemma common_multiple_formula_correct (M : Model) (rho : nat -> carrier M)
    (n : carrier M) :
  holds M (n .: rho) common_multiple_formula <->
    exists m, positive_common_multiple M n m.
Proof.
  unfold holds, common_multiple_formula, Peano.sless,
    positive_common_multiple, coding_lt.
  cbn.
  reflexivity.
Qed.

Lemma positive_product (M : Model) (x y : carrier M) :
  coding_lt M (zeroM M) x -> coding_lt M (zeroM M) y ->
  coding_lt M (zeroM M) (mulM M x y).
Proof.
  intros [a Ha] [b Hb].
  rewrite coding_add_zero in Ha, Hb. subst x y.
  pose proof (@Peano.mult_rec (carrier M) (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) (succM M b) a) as Hmul.
  change (mulM M (succM M a) (succM M b) =
    addM M (succM M b) (mulM M a (succM M b))) in Hmul.
  rewrite Hmul.
  pose proof (@Peano.add_rec (carrier M) (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) b (mulM M a (succM M b))) as Hadd.
  change (addM M (succM M b) (mulM M a (succM M b)) =
    succM M (addM M b (mulM M a (succM M b)))) in Hadd.
  rewrite Hadd.
  apply coding_zero_lt_succ.
Qed.

Lemma positive_common_multiple_total (M : Model) (n : carrier M) :
  exists m, positive_common_multiple M n m.
Proof.
  apply (definable_induction M
    (fun n => exists m, positive_common_multiple M n m)).
  - exists common_multiple_formula, (fun _ => zeroM M).
    intro x. symmetry. apply common_multiple_formula_correct.
  - exists (succM M (zeroM M)). split; [apply coding_zero_lt_succ|].
    intros d [Hd Hbound].
    apply (@Peano.lt_S (carrier M) (raw_interpretation M)
      (fun ax H rho => axioms M ax rho H) d (zeroM M)) in Hbound.
    destruct Hbound as [Hbound | ->].
    + exfalso. exact (@Peano.nolessthen_zero (carrier M)
        (raw_interpretation M) (fun ax H rho => axioms M ax rho H) d Hbound).
    + exfalso. exact (@Peano.nolessthen_zero (carrier M)
        (raw_interpretation M) (fun ax H rho => axioms M ax rho H) (zeroM M) Hd).
  - intros x [m [Hm Hdiv]]. exists (mulM M m (succM M x)).
    split; [apply positive_product; [exact Hm|apply coding_zero_lt_succ]|].
    intros d [Hd Hbound].
    apply (@Peano.lt_S (carrier M) (raw_interpretation M)
      (fun ax H rho => axioms M ax rho H) d (succM M x)) in Hbound.
    destruct Hbound as [Hbound | ->].
    + destruct (Hdiv d (conj Hd Hbound)) as [k Hk].
      exists (mulM M k (succM M x)). rewrite Hk.
      exact (@Peano.mult_asso (carrier M) (raw_interpretation M)
        (fun ax H rho => axioms M ax rho H) d k (succM M x)).
    + exists m. exact (@Peano.mult_comm (carrier M) (raw_interpretation M)
        (fun ax H rho => axioms M ax rho H) m (succM M x)).
Qed.

