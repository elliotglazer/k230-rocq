(** PA-definable invariant for a bounded source proof trace. Each sequent
    is interpreted in every combined context at every sufficiently large
    domain bound. The branch case is a real FullND branch derivation. *)
From PAModel Require Import Model Arithmetic FiniteCoding NumericalProofs
  NumericalSourceFull NumericalContexts SourceSequents SourceTraceBounds SentenceBounds
  SourceRelativization SourceRelativeContexts.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_relative_sequent M domain bound r :=
  forall b c n f,source_sequent M b c n f r ->
  forall k u v l g,coding_lt M bound (succM M k) ->
    source_relative_context M domain b c n k u v l ->
    source_relativization M domain f g -> source_full_prv M u v l g.

Definition source_relative_branches M domain bound r :=
  forall b c n a d f,source_branches M b c n a d f r ->
  forall k u v l ra rd rf,coding_lt M bound (succM M k) ->
    source_relative_context M domain b c n k u v l ->
    source_relativization M domain a ra -> source_relativization M domain d rd ->
    source_relativization M domain f rf -> source_full_branches M u v l ra rd rf.

Definition source_relative_good M domain bound r :=
  source_row_at_bound M r bound /\
  source_relative_sequent M domain bound r /\ source_relative_branches M domain bound r.

Definition source_relative_sequent_formula : form :=
  ∀∀∀∀ (source_sequent_formula $3 $2 $1 $0 $4 →
  ∀∀∀∀∀ (Peano.sless $10 (σ $4) →
    source_relative_context_formula $11 $8 $7 $6 $4 $3 $2 $1 →
    source_relativization_formula $11 $5 $0 → source_full_prv_formula $3 $2 $1 $0)).

Definition source_relative_branches_formula : form :=
  ∀∀∀∀∀∀ (source_branches_formula $5 $4 $3 $2 $1 $0 $6 →
  ∀∀∀∀∀∀∀ (Peano.sless $14 (σ $6) →
    source_relative_context_formula $15 $12 $11 $10 $6 $5 $4 $3 →
    source_relativization_formula $15 $9 $2 → source_relativization_formula $15 $8 $1 →
    source_relativization_formula $15 $7 $0 → source_full_branches_formula $5 $4 $3 $2 $1 $0)).

Definition source_relative_good_formula : form :=
  source_row_at_bound_formula $0 $1 ∧
    (source_relative_sequent_formula ∧ source_relative_branches_formula).

Local Opaque holds source_sequent_formula source_branches_formula source_row_at_bound_formula
  source_relative_context_formula source_relativization_formula source_full_prv_formula
  source_full_branches_formula Peano.sless.

Theorem source_relative_good_formula_correct M rho :
  holds M rho source_relative_good_formula <->
  source_relative_good M (rho 2) (rho 1) (rho 0).
Proof.
  unfold source_relative_good_formula,source_relative_good.
  rewrite holds_and,holds_and,source_row_at_bound_formula_correct.
  unfold source_relative_sequent_formula,source_relative_sequent,
    source_relative_branches_formula,source_relative_branches.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite source_sequent_formula_correct. setoid_rewrite source_branches_formula_correct.
  setoid_rewrite less_formula_correct. setoid_rewrite source_relative_context_formula_correct.
  setoid_rewrite source_relativization_formula_correct.
  setoid_rewrite source_full_prv_formula_correct. setoid_rewrite source_full_branches_formula_correct.
  reflexivity.
Qed.

Theorem source_relative_good_definable M domain bound :
  Definable1 M (source_relative_good M domain bound).
Proof.
  exists source_relative_good_formula,(bound .: domain .: fun _=>zeroM M).
  intro r. symmetry. apply source_relative_good_formula_correct.
Qed.

Theorem source_relative_sequent_intro M domain bound r b c n f :
  source_row_at_bound M r bound -> source_sequent M b c n f r ->
  (forall k u v l g,coding_lt M bound (succM M k) ->
    source_relative_context M domain b c n k u v l ->
    source_relativization M domain f g -> source_full_prv M u v l g) ->
  source_relative_good M domain bound r.
Proof.
  intros HB HR H. split;[exact HB|]. split.
  - intros b' c' n' f' HR'.
    destruct (source_sequent_injective M b c n f b' c' n' f' r HR HR') as [<- [<- [<- <-]]].
    exact H.
  - intros b' c' n' a d f' HR'. exfalso.
    exact (source_row_kinds_disjoint M b c n f b' c' n' a d f' r HR HR').
Qed.

Theorem source_relative_branches_intro M domain bound r b c n a d f :
  source_row_at_bound M r bound -> source_branches M b c n a d f r ->
  (forall k u v l ra rd rf,coding_lt M bound (succM M k) ->
    source_relative_context M domain b c n k u v l ->
    source_relativization M domain a ra -> source_relativization M domain d rd ->
    source_relativization M domain f rf -> source_full_branches M u v l ra rd rf) ->
  source_relative_good M domain bound r.
Proof.
  intros HB HR H. split;[exact HB|]. split.
  - intros b' c' n' f' HR'. exfalso.
    exact (source_row_kinds_disjoint M b' c' n' f' b c n a d f r HR' HR).
  - intros b' c' n' a' d' f' HR'.
    destruct (source_branches_injective M b c n a d f b' c' n' a' d' f' r HR HR')
      as [<- [<- [<- [<- [<- <-]]]]]. exact H.
Qed.

Theorem source_relative_good_formula_bound : bounded 3 source_relative_good_formula.
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

Print Assumptions source_relative_good_formula_correct.
Print Assumptions source_relative_good_definable.
Print Assumptions source_relative_sequent_intro.
Print Assumptions source_relative_branches_intro.
