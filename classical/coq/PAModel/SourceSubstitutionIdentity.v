(** Internal substitution is the identity when its finite map fixes all free
    indices.  This applies to nonstandard source formula codes and bounds. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT FiniteCRTFormula CodeExpressions NumericalProofs
  NumericalEnvironments SetFormulaCodes SetCodeDescent SourceBounded
  NumericalSubstitutionMaps NumericalSubstitution.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition substitution_fixes_bound M b c n base k :=
  forall i, coding_lt M i k -> substitution_lookup M b c n base i i.

Definition substitution_fixes_bound_formula (b c n base k : term) : form :=
  ∀ (Peano.sless $0 (k`[↑]) →
    substitution_lookup_formula (b`[↑]) (c`[↑]) (n`[↑]) (base`[↑]) $0 $0).

Local Opaque holds substitution_lookup_formula.
Lemma substitution_fixes_bound_formula_correct M rho b c n base k :
  holds M rho (substitution_fixes_bound_formula b c n base k) <->
  substitution_fixes_bound M (evalM M rho b) (evalM M rho c)
    (evalM M rho n) (evalM M rho base) (evalM M rho k).
Proof.
  unfold substitution_fixes_bound_formula,substitution_fixes_bound.
  setoid_rewrite holds_all. setoid_rewrite holds_imp.
  setoid_rewrite holds_sless. setoid_rewrite substitution_lookup_formula_correct.
  unfold evalM. repeat setoid_rewrite eval_up. reflexivity.
Qed.

Lemma substitution_lift_fixes_bound M b c n base d e m k :
  substitution_lift M b c n base d e m ->
  substitution_fixes_bound M b c n base k ->
  substitution_fixes_bound M d e m (succM M base) (succM M k).
Proof.
  intros HL HF i Hi.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) i) as [E|[i' E]]; subst i.
  - exact (proj2 (substitution_lift_head M b c n base d e m (zeroM M) HL) eq_refl).
  - apply (proj2 (substitution_lift_tail M b c n base d e m i' i' HL)).
    apply HF. exact (proj1 (coding_lt_succ_cancel M i' k) Hi).
Qed.

Definition source_substitution_identity_property M f := forall b c n base k,
  source_bounded M f k -> substitution_fixes_bound M b c n base k ->
  numerical_substitution M f b c n base f.

Definition source_substitution_identity_formula : form :=
  ∀∀∀∀∀ (source_bounded_accept_formula $5 $0 →
    substitution_fixes_bound_formula $4 $3 $2 $1 $0 →
    numerical_substitution_formula $5 $4 $3 $2 $1 $5).

Local Opaque source_bounded_accept_formula substitution_fixes_bound_formula
  numerical_substitution_formula.
Lemma source_substitution_identity_definable M :
  Definable1 M (source_substitution_identity_property M).
Proof.
  exists source_substitution_identity_formula,(fun _=>zeroM M). intro f.
  unfold source_substitution_identity_formula,source_substitution_identity_property.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite source_bounded_accept_formula_correct.
  setoid_rewrite substitution_fixes_bound_formula_correct.
  setoid_rewrite numerical_substitution_formula_correct. reflexivity.
Qed.

Theorem numerical_substitution_identity_on_bound M f :
  source_substitution_identity_property M f.
Proof.
  revert f. apply (sf_code_induction M (source_substitution_identity_property M)).
  - apply source_substitution_identity_definable.
  - intros b c n base k _ _.
    apply (proj2 (numerical_substitution_invalid M (zeroM M) b c n base
      (zeroM M) (or_introl eq_refl))). reflexivity.
  - intros f Hbad b c n base k HF _. exfalso.
    exact (source_bounded_reject_invalid M f k Hbad HF).
  - intros a d f Hf b c n base k HF Hfix.
    destruct (proj1 (source_bounded_accept_atom M SFMember a d f k
      (or_introl eq_refl) Hf) HF) as [Ha Hd].
    apply (proj2 (numerical_substitution_member M a d f b c n base f Hf)).
    exists a,d. repeat split;auto.
  - intros a d f Hf b c n base k HF Hfix.
    destruct (proj1 (source_bounded_accept_atom M SFEqual a d f k
      (or_intror eq_refl) Hf) HF) as [Ha Hd].
    apply (proj2 (numerical_substitution_equal M a d f b c n base f Hf)).
    exists a,d. repeat split;auto.
  - intros h a d f Hh Hf IHa IHd b c n base k HF Hfix.
    destruct (proj1 (source_bounded_accept_binary M h a d f k Hh Hf) HF)
      as [HA HD].
    apply (proj2 (numerical_substitution_binary M h a d f b c n base f Hh Hf)).
    exists a,d. split;[exact (IHa b c n base k HA Hfix)|].
    split;[exact (IHd b c n base k HD Hfix)|exact Hf].
  - intros h a f Hh Hf IH b c n base k HF Hfix.
    pose proof (proj1 (source_bounded_accept_unary M h a f k Hh Hf) HF) as HA.
    destruct (substitution_lift_total M b c n base) as [d [e [m HL]]].
    pose proof (IH d e m (succM M base) (succM M k) HA
      (substitution_lift_fixes_bound M b c n base d e m k HL Hfix)) as HR.
    destruct Hh as [E|E];subst h.
    + apply (proj2 (numerical_substitution_quantifier M true a f b c n base f Hf)).
      exists d,e,m,a. auto.
    + apply (proj2 (numerical_substitution_quantifier M false a f b c n base f Hf)).
      exists d,e,m,a. auto.
Qed.

Corollary numerical_substitution_lift_fixes_domain M domain b c n base d e m :
  source_bounded M domain (code_numeral M 1) ->
  substitution_lift M b c n base d e m ->
  numerical_substitution M domain d e m (succM M base) domain.
Proof.
  intros HD HL. apply (numerical_substitution_identity_on_bound M domain d e m
    (succM M base) (code_numeral M 1) HD).
  change (substitution_fixes_bound M d e m (succM M base) (succM M (zeroM M))).
  apply (substitution_lift_fixes_bound M b c n base d e m (zeroM M) HL).
  intros i Hi. exfalso. exact (coding_not_lt_zero M i Hi).
Qed.

Print Assumptions numerical_substitution_identity_on_bound.
Print Assumptions numerical_substitution_lift_fixes_domain.





