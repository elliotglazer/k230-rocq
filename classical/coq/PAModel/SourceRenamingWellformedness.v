From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs BoundedCollection
  NumericalRenamingMaps NumericalRenaming NumericalContextRenaming NumericalContexts
  SourceRenamingBounds SourceBounded SourceSequents.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Theorem source_renaming_range_bound M rb rc rn delta k :
  exists l,renaming_maps_bound M rb rc rn delta k l.
Proof.
  set (rho:=delta .: rn .: rc .: rb .: fun _=>zeroM M).
  set (phi:=renaming_lookup_formula $5 $4 $3 $2 $1 $0).
  assert (HT:forall i,coding_lt M i k -> exists j,holds M (j .: i .: rho) phi).
  { intros i _. destruct (renaming_lookup_total M rb rc rn delta i) as [j HJ].
    exists j. apply (proj2 (renaming_lookup_formula_correct M (j .: i .: rho)
      $5 $4 $3 $2 $1 $0)). exact HJ. }
  destruct (bounded_collection M phi rho k HT) as [l HL].
  exists l. intros i j HI HJ.
  destruct (HL i HI) as [v [HV HP]].
  apply (proj1 (renaming_lookup_formula_correct M (v .: i .: rho) $5 $4 $3 $2 $1 $0)) in HP.
  pose proof (renaming_lookup_functional M rb rc rn delta i j v HJ HP) as E. now subst v.
Qed.

Theorem source_renaming_sequent_wf M b c n f rb rc rn delta ub uc g :
  source_sequent_wf M b c n f -> context_renaming M b c n rb rc rn delta ub uc ->
  numerical_renaming M f rb rc rn delta g -> source_sequent_wf M ub uc n g.
Proof.
  intros [k [HF HC]] HContext HR.
  destruct (source_renaming_range_bound M rb rc rn delta k) as [l HL].
  exists l. split.
  - exact (numerical_renaming_preserves_bound M f rb rc rn delta g k l HF HR HL).
  - exact (context_renaming_preserves_bound M b c n rb rc rn delta ub uc k l HContext HC HL).
Qed.

Theorem source_renaming_branches_wf M b c n a d f rb rc rn delta ub uc ar dr fr :
  source_branches_wf M b c n a d f -> context_renaming M b c n rb rc rn delta ub uc ->
  numerical_renaming M a rb rc rn delta ar -> numerical_renaming M d rb rc rn delta dr ->
  numerical_renaming M f rb rc rn delta fr -> source_branches_wf M ub uc n ar dr fr.
Proof.
  intros [k [HA [HD [HF HC]]]] HContext HRA HRD HRF.
  destruct (source_renaming_range_bound M rb rc rn delta k) as [l HL].
  exists l. repeat split.
  - exact (numerical_renaming_preserves_bound M a rb rc rn delta ar k l HA HRA HL).
  - exact (numerical_renaming_preserves_bound M d rb rc rn delta dr k l HD HRD HL).
  - exact (numerical_renaming_preserves_bound M f rb rc rn delta fr k l HF HRF HL).
  - exact (context_renaming_preserves_bound M b c n rb rc rn delta ub uc k l HContext HC HL).
Qed.

Print Assumptions source_renaming_range_bound.
Print Assumptions source_renaming_sequent_wf.
Print Assumptions source_renaming_branches_wf.
