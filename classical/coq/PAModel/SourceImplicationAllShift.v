(** Move one universal past an implication while shifting the ambient
    context and its antecedent. This is an actual numerical proof macro. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
  SourceBounded NumericalContexts NumericalEnvironments NumericalContextRenaming
  NumericalRenaming SourceRenamingBounds SourceQuantifierRules SourceShiftSpecialization
  SourceProofRenaming SourceProofWeakening NumericalSourceFull.
Unset Implicit Arguments.

Lemma source_shift_bound M f g k : source_bounded M f k ->
  source_formula_shift M f g -> source_bounded M g (succM M k).
Proof.
  intros HF HS.
  apply (numerical_renaming_preserves_bound M f (zeroM M) (zeroM M) (zeroM M)
    (succM M (zeroM M)) g k (succM M k) HF HS).
  intros i j Hi Hj. apply context_shift_lookup in Hj. subst j.
  exact (proj2 (coding_lt_succ_cancel M i k) Hi).
Qed.

Theorem source_full_implication_all_shift M b c n p a all imp u v ps out :
  sf_relation M SFAll a (zeroM M) all -> sf_relation M SFImpl p all imp ->
  context_shift M b c n u v -> source_formula_shift M p ps ->
  sf_relation M SFImpl ps a out -> source_full_prv M b c n imp ->
  source_full_prv M u v n out.
Proof.
  intros HAll HImp HC HPS HOut HP.
  destruct (source_full_prv_wellformed M b c n imp HP) as [k [HBound HCtx]].
  destruct (proj1 (source_bounded_accept_binary M SFImpl p all imp k
    (or_intror (or_intror eq_refl)) HImp) HBound) as [HPBound HAllBound].
  pose proof (proj1 (source_bounded_accept_unary M SFAll a all k
    (or_introl eq_refl) HAll) HAllBound) as HABound.
  pose proof (source_shift_bound M p ps k HPBound HPS) as HPSBound.
  pose proof (context_shift_preserves_bound M b c n u v k HC HCtx) as HUCtx.
  destruct (numerical_renaming_total M all (zeroM M) (zeroM M) (zeroM M)
    (succM M (zeroM M))) as [sa HSA].
  pose proof (source_shift_bound M all sa k HAllBound HSA) as HSABound.
  destruct (sf_relation_total M SFImpl ps sa) as [si HSI].
  assert (HR:numerical_renaming M imp (zeroM M) (zeroM M) (zeroM M)
    (succM M (zeroM M)) si).
  { apply (proj2 (numerical_renaming_binary M SFImpl p all imp
      (zeroM M) (zeroM M) (zeroM M) (succM M (zeroM M)) si
      (or_intror (or_intror eq_refl)) HImp)). exists ps,sa. auto. }
  pose proof (source_full_prv_renaming M b c n imp (zeroM M) (zeroM M) (zeroM M)
    (succM M (zeroM M)) u v si HP HC HR) as PSI.
  destruct (source_shifted_all_specialization M a all sa (succM M k) HABound HAll HSA)
    as [ar [HAr HInst]].
  destruct (environment_cons_total M u v n ps) as [cb [cc [cn HCons]]].
  assert (HCCtx:context_bounded M cb cc cn (succM M k)).
  { apply (proj2 (context_bounded_cons M u v n ps cb cc cn (succM M k) HCons)). auto. }
  assert (HWeak:forall f,source_full_prv M u v n f -> source_full_prv M cb cc cn f).
  { intros f PF. apply (source_full_prv_weaken_bounded M u v n cb cc cn f (succM M k) PF).
    - intros h HH. apply (proj2 (context_member_cons M u v n ps cb cc cn h HCons)). now right.
    - exact HCCtx. }
  apply (full_source_II M u v n ps a out cb cc cn).
  - exists (succM M k). split;[|exact HUCtx].
    apply (proj2 (source_bounded_accept_binary M SFImpl ps a out (succM M k)
      (or_intror (or_intror eq_refl)) HOut)). auto.
  - apply (full_source_AllE M cb cc cn ar sa (zeroM M) a).
    + exists (succM M k). auto.
    + apply (full_source_IE M cb cc cn ps sa si).
      * exists (succM M k). auto.
      * exact (HWeak si PSI).
      * apply full_source_Ctx.
        -- exists (succM M k). auto.
        -- apply (proj2 (context_member_cons M u v n ps cb cc cn ps HCons)). now left.
      * exact HSI.
    + exact HAr.
    + exact HInst.
  - exact HCons.
  - exact HOut.
Qed.

Print Assumptions source_shift_bound.
Print Assumptions source_full_implication_all_shift.
