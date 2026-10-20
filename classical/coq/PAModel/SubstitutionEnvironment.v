(** Bounded agreement between an environment and its composition with a
    de Bruijn substitution. This is a condition, not an existence axiom. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  NumericalProofs SentenceBounds NumericalEnvironments NumericalSubstitutionMaps.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition substitution_environment_agreement M sb sc sn base eb ec en fb fc fn bound :=
  forall i x y z, coding_lt M i bound ->
    substitution_lookup M sb sc sn base i x ->
    environment_lookup M eb ec en x y ->
    environment_lookup M fb fc fn i z -> y=z.

(** The four quantified slots are i=$3, x=$2, y=$1, z=$0. *)
Definition substitution_environment_agreement_formula
    (sb sc sn base eb ec en fb fc fn bound : term) : form :=
  ∀∀∀∀ (Peano.sless $3 (lift4 bound) →
    substitution_lookup_formula (lift4 sb) (lift4 sc) (lift4 sn) (lift4 base) $3 $2 →
    environment_lookup_formula (lift4 eb) (lift4 ec) (lift4 en) $2 $1 →
    environment_lookup_formula (lift4 fb) (lift4 fc) (lift4 fn) $3 $0 → $1 == $0).

Local Opaque holds Peano.sless substitution_lookup_formula environment_lookup_formula.
Lemma substitution_environment_agreement_formula_correct M rho
    sb sc sn base eb ec en fb fc fn bound :
  holds M rho (substitution_environment_agreement_formula sb sc sn base eb ec en fb fc fn bound) <->
  substitution_environment_agreement M
    (evalM M rho sb) (evalM M rho sc) (evalM M rho sn) (evalM M rho base)
    (evalM M rho eb) (evalM M rho ec) (evalM M rho en)
    (evalM M rho fb) (evalM M rho fc) (evalM M rho fn) (evalM M rho bound).
Proof.
  unfold substitution_environment_agreement_formula,substitution_environment_agreement.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite less_formula_correct. setoid_rewrite substitution_lookup_formula_correct.
  setoid_rewrite environment_lookup_formula_correct. setoid_rewrite lift4_correct.
  reflexivity.
Qed.

Theorem substitution_environment_agreement_lift M
    sb sc sn base eb ec en fb fc fn bound fresh
    sb' sc' sn' eb' ec' en' fb' fc' fn' :
  substitution_environment_agreement M sb sc sn base eb ec en fb fc fn bound ->
  substitution_lift M sb sc sn base sb' sc' sn' ->
  environment_cons M eb ec en fresh eb' ec' en' ->
  environment_cons M fb fc fn fresh fb' fc' fn' ->
  substitution_environment_agreement M sb' sc' sn' (succM M base)
    eb' ec' en' fb' fc' fn' (succM M bound).
Proof.
  intros H Hsub HE HF i x y z Hi Hix Hxy Hiz.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax Ha rho => axioms M ax rho Ha) i) as [Ei|[j Ei]]; subst i.
  - apply (proj1 (substitution_lift_head M sb sc sn base sb' sc' sn' x Hsub)) in Hix.
    subst x. apply (environment_cons_head M eb ec en fresh eb' ec' en' y HE) in Hxy.
    apply (environment_cons_head M fb fc fn fresh fb' fc' fn' z HF) in Hiz.
    congruence.
  - destruct (substitution_lift_tail_inv M sb sc sn base sb' sc' sn' j x Hsub Hix)
      as [a [Hja Ex]]. subst x.
    apply (environment_cons_tail M eb ec en fresh eb' ec' en' a y HE) in Hxy.
    apply (environment_cons_tail M fb fc fn fresh fb' fc' fn' j z HF) in Hiz.
    exact (H j a y z (proj1 (coding_lt_succ_cancel M j bound) Hi) Hja Hxy Hiz).
Qed.

Lemma substitution_environment_agreement_formula_bound :
  bounded 11 (substitution_environment_agreement_formula
    $0 $1 $2 $3 $4 $5 $6 $7 $8 $9 $10).
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

Print Assumptions substitution_environment_agreement_formula_correct.
Print Assumptions substitution_environment_agreement_lift.
Print Assumptions substitution_environment_agreement_formula_bound.
