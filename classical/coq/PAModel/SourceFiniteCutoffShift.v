(** Capture-avoiding shifts under a fixed number of source binders. Source
    codes and all free-index bounds remain arbitrary PA-model elements. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions NumericalProofs
  NumericalSubstitutionMaps NumericalSubstitution SourceSubstitutionBounds SubstitutionSource
  SetFormulaCodes ZFCFiniteSourceCodes SentenceBounds.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Fixpoint source_succ_iter M (depth:nat) (k:carrier M) :=
  match depth with 0=>k | S d=>succM M (source_succ_iter M d k) end.
Fixpoint source_shift_sigma (depth:nat) : nat->sf_term :=
  match depth with 0 => (fun i => var (S i)) | S d=>up (source_shift_sigma d) end.

Fixpoint source_cutoff_shift_map M (depth:nat) (b c n:carrier M) : Prop :=
  match depth with
  | 0=>b=zeroM M /\ c=zeroM M /\ n=zeroM M
  | S d=>exists u v m,source_cutoff_shift_map M d u v m /\
      substitution_lift M u v m (code_numeral M (S d)) b c n
  end.
Fixpoint source_cutoff_shift_map_formula (depth:nat) (b c n:term) : form :=
  match depth with
  | 0=>b==zero ∧ (c==zero ∧ n==zero)
  | S d=>∃∃∃ (source_cutoff_shift_map_formula d $2 $1 $0 ∧
      substitution_lift_formula $2 $1 $0 (num (S d)) (lift3 b) (lift3 c) (lift3 n))
  end.
Local Opaque holds substitution_lift_formula.

Theorem source_cutoff_shift_map_formula_correct M depth rho b c n :
  holds M rho (source_cutoff_shift_map_formula depth b c n) <->
  source_cutoff_shift_map M depth (evalM M rho b) (evalM M rho c) (evalM M rho n).
Proof.
  revert rho b c n. induction depth as [|d IH];intros rho b c n;cbn -[num code_numeral evalM].
  - repeat rewrite holds_and. reflexivity.
  - repeat setoid_rewrite holds_ex. setoid_rewrite holds_and.
    setoid_rewrite IH. setoid_rewrite substitution_lift_formula_correct.
    repeat setoid_rewrite code_eval_num. unfold evalM,lift3. repeat setoid_rewrite eval_up. reflexivity.
Qed.

Theorem source_cutoff_shift_map_total M depth : exists b c n,source_cutoff_shift_map M depth b c n.
Proof.
  induction depth as [|d [u [v [m HM]]]].
  - exists (zeroM M),(zeroM M),(zeroM M). repeat split;reflexivity.
  - destruct (substitution_lift_total M u v m (code_numeral M (S d))) as (b & c & n & HL).
    exists b,c,n,u,v,m. auto.
Qed.

Lemma source_cutoff_shift_base_lookup M i :
  substitution_lookup M (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1) i (succM M i).
Proof.
  right. split;[apply coding_not_lt_zero|]. exists i.
  split;[symmetry;apply coding_add_zero|].
  change (succM M i = addM M (succM M (zeroM M)) i).
  now rewrite Arithmetic.add_succ,coding_add_zero.
Qed.

Theorem source_cutoff_shift_map_bounds M depth b c n k :
  source_cutoff_shift_map M depth b c n ->
  substitution_maps_bound M b c n (code_numeral M (S depth))
    (source_succ_iter M depth k) (source_succ_iter M (S depth) k).
Proof.
  revert b c n. induction depth as [|d IH];intros b c n HM.
  - destruct HM as [-> [-> ->]]. intros i j Hi Hj.
    assert (E : j = succM M i) by (eapply substitution_lookup_functional;[exact Hj|apply source_cutoff_shift_base_lookup]).
    subst j. apply coding_lt_succ_cancel. exact Hi.
  - destruct HM as (u & v & m & HM & HL). cbn [source_succ_iter].
    exact (substitution_lift_maps_bound M u v m (code_numeral M (S d)) b c n
      (source_succ_iter M d k) (source_succ_iter M (S d) k) HL (IH u v m HM)).
Qed.

Theorem source_cutoff_shift_map_fixed_lookup M depth b c n :
  source_cutoff_shift_map M depth b c n -> forall i,
  substitution_lookup M b c n (code_numeral M (S depth)) (code_numeral M i)
    (code_numeral M (sf_index (source_shift_sigma depth i))).
Proof.
  revert b c n. induction depth as [|d IH];intros b c n HM i.
  - destruct HM as [-> [-> ->]]. apply source_cutoff_shift_base_lookup.
  - destruct HM as (u & v & m & HM & HL).
    exact (substitution_source_lift_lookup M u v m (code_numeral M (S d)) b c n
      (source_shift_sigma d) HL (IH u v m HM) i).
Qed.

Definition source_cutoff_shift M depth f g := exists b c n,
  source_cutoff_shift_map M depth b c n /\
  numerical_substitution M f b c n (code_numeral M (S depth)) g.
Definition source_cutoff_shift_formula depth (f g:term) : form :=
  ∃∃∃ (source_cutoff_shift_map_formula depth $2 $1 $0 ∧
    numerical_substitution_formula (lift3 f) $2 $1 $0 (num (S depth)) (lift3 g)).
Local Opaque source_cutoff_shift_map_formula numerical_substitution_formula.
Theorem source_cutoff_shift_formula_correct M depth rho f g :
  holds M rho (source_cutoff_shift_formula depth f g) <->
  source_cutoff_shift M depth (evalM M rho f) (evalM M rho g).
Proof.
  unfold source_cutoff_shift_formula,source_cutoff_shift.
  repeat setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite source_cutoff_shift_map_formula_correct.
  setoid_rewrite numerical_substitution_formula_correct.
  repeat setoid_rewrite code_eval_num. unfold evalM,lift3. repeat setoid_rewrite eval_up. reflexivity.
Qed.

Theorem source_cutoff_shift_total M depth f : exists g,source_cutoff_shift M depth f g.
Proof.
  destruct (source_cutoff_shift_map_total M depth) as (b & c & n & HM).
  destruct (numerical_substitution_total M f b c n (code_numeral M (S depth))) as [g HG].
  exists g,b,c,n. auto.
Qed.

Theorem source_cutoff_shift_bounded M depth f g k :
  SourceBounded.source_bounded M f (source_succ_iter M depth k) ->
  source_cutoff_shift M depth f g ->
  SourceBounded.source_bounded M g (source_succ_iter M (S depth) k).
Proof.
  intros HF (b & c & n & HM & HG).
  exact (numerical_substitution_preserves_bound M f b c n (code_numeral M (S depth)) g
    (source_succ_iter M depth k) (source_succ_iter M (S depth) k) HF HG
    (source_cutoff_shift_map_bounds M depth b c n k HM)).
Qed.

Theorem source_cutoff_shift_fixed_source M depth rho (phi:sf_form) f g :
  code_relation M rho (sf_expression phi) f ->
  code_relation M rho (sf_expression (phi[source_shift_sigma depth])) g ->
  source_cutoff_shift M depth f g.
Proof.
  intros HF HG. destruct (source_cutoff_shift_map_total M depth) as (b & c & n & HM).
  exists b,c,n. split;[exact HM|].
  exact (fixed_source_substitution M rho phi (source_shift_sigma depth) b c n
    (code_numeral M (S depth)) f g (source_cutoff_shift_map_fixed_lookup M depth b c n HM) HF HG).
Qed.

Print Assumptions source_cutoff_shift_map_formula_correct.
Print Assumptions source_cutoff_shift_map_total.
Print Assumptions source_cutoff_shift_map_bounds.
Print Assumptions source_cutoff_shift_formula_correct.
Print Assumptions source_cutoff_shift_total.
Print Assumptions source_cutoff_shift_bounded.
Print Assumptions source_cutoff_shift_fixed_source.
