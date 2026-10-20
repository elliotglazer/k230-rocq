(** Source proof constructors with their finite wellformedness inferred
    from actual premises. No source truth or semantic interpretation occurs. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension CodeExpressions
  SetFormulaCodes SourceBounded SourceBoundMonotone SourceSequents SourceTraceBounds
  NumericalContexts NumericalEnvironments NumericalContextRenaming NumericalRenaming
  NumericalSourceFull SourceContextTransport SourceContextProofHelpers SourceInstantiationConstructors
  SourceConjunctionRules SourceExistentialMap SourceProofRenaming SourceWitnessDeltaShift
  SourceUpperWitnessRecipes.
Unset Implicit Arguments.

Theorem source_full_conjunction M b c n a d f :
  sf_relation M SFAnd a d f -> source_full_prv M b c n a ->
  source_full_prv M b c n d -> source_full_prv M b c n f.
Proof.
  intros HG PA PD. apply (full_source_CI M b c n a d f);try assumption.
  exact (source_wf_binary M b c n SFAnd a d f (or_introl eq_refl) HG
    (source_full_prv_wellformed M b c n a PA) (source_full_prv_wellformed M b c n d PD)).
Qed.

Theorem source_full_implication_intro M b c n a d f u v l :
  environment_cons M b c n a u v l -> sf_relation M SFImpl a d f ->
  source_full_prv M u v l d -> source_full_prv M b c n f.
Proof.
  intros HCons HG PD.
  destruct (source_full_prv_wellformed M u v l d PD) as [k [HD HC]].
  apply (proj1 (context_bounded_cons M b c n a u v l k HCons)) in HC.
  destruct HC as [HA HCtx].
  apply (full_source_II M b c n a d f u v l);try assumption.
  exists k. split;[|exact HCtx].
  apply (proj2 (source_bounded_accept_binary M SFImpl a d f k
    (or_intror (or_intror eq_refl)) HG));auto.
Qed.

Theorem source_full_all_intro M b c n a f u v :
  source_context_finite_bound M b c n ->context_shift M b c n u v ->
  sf_relation M SFAll a (zeroM M) f -> source_full_prv M u v n a ->
  source_full_prv M b c n f.
Proof.
  intros [j HC] HShift HAll PA.
  destruct (source_full_prv_wellformed M u v n a PA) as [k [HA _]].
  apply (full_source_AllI M b c n a f u v);try assumption.
  exists (addM M k j). split.
  - apply (proj2 (source_bounded_accept_unary M SFAll a f (addM M k j)
      (or_introl eq_refl) HAll)).
    apply (source_bounded_monotone M a k (succM M (addM M k j)) HA).
    apply (coding_lt_trans M k (succM M (addM M k j))
      (succM M (succM M (addM M k j))));[apply coding_le_add|apply coding_lt_succ].
  - apply (context_bounded_monotone M b c n j (addM M k j) HC).
    rewrite Arithmetic.add_comm. apply coding_le_add.
Qed.

Theorem source_full_weaken_cons_finite M b c n a u v l f :
  environment_cons M b c n a u v l ->source_context_finite_bound M u v l ->
  source_full_prv M b c n f ->source_full_prv M u v l f.
Proof. intros HH [k HK] HP. exact (source_full_cons_weaken M b c n a u v l k f HH HK HP). Qed.

Theorem source_full_assume M b c n a u v l :
  source_sequent_wf M b c n a ->environment_cons M b c n a u v l ->
  source_context_finite_bound M u v l /\source_full_prv M u v l a.
Proof.
  intros [k [HA HC]] HCons.
  assert (HB:context_bounded M u v l k).
  { apply (proj2 (context_bounded_cons M b c n a u v l k HCons));auto. }
  split;[now exists k|]. exact (source_full_cons_head M b c n a u v l k HCons HA HB).
Qed.

Theorem source_full_exists_conjunction_swap M b c n a d pair swapped ex oldex :
  sf_relation M SFAnd a d pair ->sf_relation M SFAnd d a swapped ->
  sf_relation M SFEx pair (zeroM M) ex ->sf_relation M SFEx swapped (zeroM M) oldex ->
  source_full_prv M b c n ex ->source_full_prv M b c n oldex.
Proof.
  intros HP HS HE HO PE.
  destruct (source_full_prv_wellformed M b c n ex PE) as [k [HBound HC]].
  pose proof (proj1 (source_bounded_accept_unary M SFEx pair ex k
    (or_intror eq_refl) HE) HBound) as HPair.
  pose proof (proj1 (source_bounded_accept_binary M SFAnd a d pair (succM M k)
    (or_introl eq_refl) HP) HPair) as HParts.
  assert (WOut:source_sequent_wf M b c n oldex).
  { exists k. split;[|exact HC].
    apply (proj2 (source_bounded_accept_unary M SFEx swapped oldex k (or_intror eq_refl) HO)).
    apply (proj2 (source_bounded_accept_binary M SFAnd d a swapped (succM M k) (or_introl eq_refl) HS));tauto. }
  destruct (context_shift_total M b c n) as [sb [sc HShift]].
  destruct (environment_cons_total M sb sc n pair) as [ub [uc [un HCons]]].
  assert (HBranch:context_bounded M ub uc un (succM M k)).
  { apply (proj2 (context_bounded_cons M sb sc n pair ub uc un (succM M k) HCons)).
    split;[exact HPair|exact (context_shift_preserves_bound M b c n sb sc k HShift HC)]. }
  pose proof (source_full_cons_head M sb sc n pair ub uc un (succM M k) HCons HPair HBranch) as PP.
  pose proof (source_full_conjunction_left M ub uc un a d pair HP PP) as PA.
  pose proof (source_full_conjunction_right M ub uc un a d pair HP PP) as PD.
  pose proof (source_full_conjunction M ub uc un d a swapped HS PD PA) as PS.
  destruct (numerical_renaming_total M oldex (zeroM M) (zeroM M) (zeroM M)
    (code_numeral M 1)) as [shifted HSR].
  exact (source_full_exists_map M b c n pair swapped ex oldex sb sc ub uc un shifted
    WOut HE HO HShift HCons HSR PE PS).
Qed.

Theorem source_full_upper_witness_closed_shift_total M cb cc cn phi k delta b closed sb sc :
  source_bounded M phi k ->source_upper_witness_closed_recipe M phi delta b closed ->
  context_shift M cb cc cn sb sc ->source_full_prv M cb cc cn closed ->
  exists shifted,source_upper_witness_closed_recipe M phi (succM M delta) (succM M b) shifted /\
    source_full_prv M sb sc cn shifted.
Proof.
  intros HP HR HC PC.
  destruct (source_upper_witness_closed_shift_total M phi k delta b closed HP HR)
    as [shifted [HS HG]].
  exists shifted. split;[exact HS|].
  exact (source_full_prv_renaming M cb cc cn closed (zeroM M)(zeroM M)(zeroM M)
    (code_numeral M 1) sb sc shifted PC HC HG).
Qed.

Print Assumptions source_full_conjunction.
Print Assumptions source_full_implication_intro.
Print Assumptions source_full_all_intro.
Print Assumptions source_full_weaken_cons_finite.
Print Assumptions source_full_assume.
Print Assumptions source_full_exists_conjunction_swap.
Print Assumptions source_full_upper_witness_closed_shift_total.
