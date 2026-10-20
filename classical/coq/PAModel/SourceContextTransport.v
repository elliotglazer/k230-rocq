(** Context inclusion and finite bounds for literal source proof transport. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension
  CodeExpressions NumericalProofs NumericalContexts NumericalEnvironments NumericalContextRenaming
  NumericalRenaming SourceBounded SourceBoundMonotone SourceTraceBounds SourceSequents.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_context_finite_bound M b c n := exists k,context_bounded M b c n k.
Definition source_context_finite_bound_formula (b c n:term) : form :=
  ∃ context_bounded_formula b`[↑] c`[↑] n`[↑] $0.
Local Opaque context_bounded_formula.
Lemma source_context_finite_bound_formula_correct M rho b c n :
  holds M rho (source_context_finite_bound_formula b c n) <->
  source_context_finite_bound M (evalM M rho b) (evalM M rho c) (evalM M rho n).
Proof.
  unfold source_context_finite_bound_formula,source_context_finite_bound.
  rewrite holds_ex. setoid_rewrite context_bounded_formula_correct.
  unfold evalM. repeat setoid_rewrite eval_up. reflexivity.
Qed.

Theorem source_wf_transport_context M b c n f u v l :
  source_sequent_wf M b c n f -> source_context_finite_bound M u v l ->
  source_sequent_wf M u v l f.
Proof.
  intros [k [HF _]] [j HC]. exists (addM M k j). split.
  - exact (source_bounded_monotone M f k (addM M k j) HF (coding_le_add M k j)).
  - apply (context_bounded_monotone M u v l j (addM M k j) HC).
    rewrite Arithmetic.add_comm. apply coding_le_add.
Qed.

Theorem source_branches_wf_transport_context M b c n a d f u v l :
  source_branches_wf M b c n a d f -> source_context_finite_bound M u v l ->
  source_branches_wf M u v l a d f.
Proof.
  intros [k [HA [HD [HF _]]]] [j HC]. exists (addM M k j). repeat split.
  - exact (source_bounded_monotone M a k (addM M k j) HA (coding_le_add M k j)).
  - exact (source_bounded_monotone M d k (addM M k j) HD (coding_le_add M k j)).
  - exact (source_bounded_monotone M f k (addM M k j) HF (coding_le_add M k j)).
  - apply (context_bounded_monotone M u v l j (addM M k j) HC).
    rewrite Arithmetic.add_comm. apply coding_le_add.
Qed.

Theorem source_context_included_cons M b c n u v l a b' c' n' u' v' l' :
  context_included M b c n u v l ->
  environment_cons M b c n a b' c' n' -> environment_cons M u v l a u' v' l' ->
  context_included M b' c' n' u' v' l'.
Proof.
  intros HI HS HT f HF.
  apply (proj2 (context_member_cons M u v l a u' v' l' f HT)).
  apply (proj1 (context_member_cons M b c n a b' c' n' f HS)) in HF.
  destruct HF as [E|HF];[now left|right;exact (HI f HF)].
Qed.

Theorem source_context_finite_bound_cons M b c n a u v l :
  source_context_finite_bound M b c n -> (exists k,source_bounded M a k) ->
  environment_cons M b c n a u v l -> source_context_finite_bound M u v l.
Proof.
  intros [j HC] [k HA] HT. exists (addM M j k).
  apply (proj2 (context_bounded_cons M b c n a u v l (addM M j k) HT)). split.
  - apply (source_bounded_monotone M a k (addM M j k) HA).
    rewrite Arithmetic.add_comm. apply coding_le_add.
  - exact (context_bounded_monotone M b c n j (addM M j k) HC (coding_le_add M j k)).
Qed.

Theorem source_context_included_shift M b c n u v l bs cs us vs :
  context_included M b c n u v l ->
  context_shift M b c n bs cs -> context_shift M u v l us vs ->
  context_included M bs cs n us vs l.
Proof.
  intros HI HS HT f HF.
  apply (proj2 (context_renaming_member_iff M u v l (zeroM M) (zeroM M)
    (zeroM M) (succM M (zeroM M)) us vs f HT)).
  apply (proj1 (context_renaming_member_iff M b c n (zeroM M) (zeroM M)
    (zeroM M) (succM M (zeroM M)) bs cs f HS)) in HF.
  destruct HF as [g [HG HR]]. exists g. split;[exact (HI g HG)|exact HR].
Qed.

Theorem source_context_finite_bound_shift M b c n u v :
  source_context_finite_bound M b c n -> context_shift M b c n u v ->
  source_context_finite_bound M u v n.
Proof.
  intros [k HK] HS. exists (succM M k).
  exact (context_shift_preserves_bound M b c n u v k HS HK).
Qed.

Print Assumptions source_wf_transport_context.
Print Assumptions source_branches_wf_transport_context.
Print Assumptions source_context_included_cons.
Print Assumptions source_context_finite_bound_cons.
Print Assumptions source_context_included_shift.
Print Assumptions source_context_finite_bound_shift.
