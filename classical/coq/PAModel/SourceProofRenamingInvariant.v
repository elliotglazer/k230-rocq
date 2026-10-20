From PAModel Require Import Model CodeExpressions NumericalProofs NumericalTraces NumericalContexts
  NumericalContextRenaming NumericalRenaming NumericalRenamingMaps NumericalSourceFull SourceSequents
  SourceQuantifierRules SourceRenamingWellformedness SetFormulaCodes SetCodeDescent RenamingPayloads.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_renaming_sequents M r := forall b c n f rb rc rn delta ub uc g,
  source_sequent M b c n f r -> context_renaming M b c n rb rc rn delta ub uc ->
  numerical_renaming M f rb rc rn delta g -> source_full_prv M ub uc n g.
Definition source_renaming_branches M r := forall b c n a d f rb rc rn delta ub uc ar dr fr,
  source_branches M b c n a d f r -> context_renaming M b c n rb rc rn delta ub uc ->
  numerical_renaming M a rb rc rn delta ar -> numerical_renaming M d rb rc rn delta dr ->
  numerical_renaming M f rb rc rn delta fr -> source_full_branches M ub uc n ar dr fr.
Definition source_proof_renaming_invariant M r :=
  source_full_row M r /\ source_renaming_sequents M r /\ source_renaming_branches M r.

Definition source_renaming_sequents_formula : form :=
  ∀∀∀∀∀∀∀∀∀∀∀ (source_sequent_formula $10 $9 $8 $7 $11 →
    context_renaming_formula $10 $9 $8 $6 $5 $4 $3 $2 $1 →
    numerical_renaming_formula $7 $6 $5 $4 $3 $0 → source_full_prv_formula $2 $1 $8 $0).
Definition source_renaming_branches_formula : form :=
  ∀∀∀∀∀∀∀∀∀∀∀∀∀∀∀ (source_branches_formula $14 $13 $12 $11 $10 $9 $15 →
    context_renaming_formula $14 $13 $12 $8 $7 $6 $5 $4 $3 →
    numerical_renaming_formula $11 $8 $7 $6 $5 $2 →
    numerical_renaming_formula $10 $8 $7 $6 $5 $1 →
    numerical_renaming_formula $9 $8 $7 $6 $5 $0 → source_full_branches_formula $4 $3 $12 $2 $1 $0).
Definition source_proof_renaming_formula : form :=
  trace_derives_formula source_full_rules $0 ∧
    (source_renaming_sequents_formula ∧ source_renaming_branches_formula).
Local Opaque holds source_sequent_formula source_branches_formula context_renaming_formula
  numerical_renaming_formula source_full_prv_formula source_full_branches_formula trace_derives_formula.

Theorem source_renaming_sequents_formula_correct M r :
  holds M (r .: fun _=>zeroM M) source_renaming_sequents_formula <-> source_renaming_sequents M r.
Proof.
  unfold source_renaming_sequents_formula,source_renaming_sequents.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite source_sequent_formula_correct. setoid_rewrite context_renaming_formula_correct.
  setoid_rewrite numerical_renaming_formula_correct. setoid_rewrite source_full_prv_formula_correct. reflexivity.
Qed.
Theorem source_renaming_branches_formula_correct M r :
  holds M (r .: fun _=>zeroM M) source_renaming_branches_formula <-> source_renaming_branches M r.
Proof.
  unfold source_renaming_branches_formula,source_renaming_branches.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite source_branches_formula_correct. setoid_rewrite context_renaming_formula_correct.
  setoid_rewrite numerical_renaming_formula_correct. setoid_rewrite source_full_branches_formula_correct. reflexivity.
Qed.
Theorem source_proof_renaming_definable M : Definable1 M (source_proof_renaming_invariant M).
Proof.
  exists source_proof_renaming_formula,(fun _=>zeroM M). intro r. symmetry.
  unfold source_proof_renaming_formula,source_proof_renaming_invariant,source_full_row.
  repeat rewrite holds_and. rewrite trace_derives_formula_correct.
  rewrite source_renaming_sequents_formula_correct,source_renaming_branches_formula_correct. reflexivity.
Qed.

Lemma source_proof_renaming_ordinary_intro M r b c n f :
  source_full_row M r -> source_sequent M b c n f r ->
  (forall rb rc rn delta ub uc g,context_renaming M b c n rb rc rn delta ub uc ->
    numerical_renaming M f rb rc rn delta g -> source_full_prv M ub uc n g) ->
  source_proof_renaming_invariant M r.
Proof.
  intros HR HS HP. split;[exact HR|]. split.
  - intros b' c' n' f' rb rc rn delta ub uc g HS' HC HG.
    destruct (source_sequent_injective M b c n f b' c' n' f' r HS HS') as [E1 [E2 [E3 E4]]].
    subst b' c' n' f'. exact (HP rb rc rn delta ub uc g HC HG).
  - intros b' c' n' a d g rb rc rn delta ub uc ar dr fr HB _ _ _ _. exfalso.
    exact (source_row_kinds_disjoint M b c n f b' c' n' a d g r HS HB).
Qed.

Lemma source_proof_renaming_branch_intro M r b c n a d f :
  source_full_row M r -> source_branches M b c n a d f r ->
  (forall rb rc rn delta ub uc ar dr fr,context_renaming M b c n rb rc rn delta ub uc ->
    numerical_renaming M a rb rc rn delta ar -> numerical_renaming M d rb rc rn delta dr ->
    numerical_renaming M f rb rc rn delta fr -> source_full_branches M ub uc n ar dr fr) ->
  source_proof_renaming_invariant M r.
Proof.
  intros HR HS HP. split;[exact HR|]. split.
  - intros b' c' n' g rb rc rn delta ub uc gr HG _ _. exfalso.
    exact (source_row_kinds_disjoint M b' c' n' g b c n a d f r HG HS).
  - intros b' c' n' a' d' f' rb rc rn delta ub uc ar dr fr HS' HC HA HD HF.
    destruct (source_branches_injective M b c n a d f b' c' n' a' d' f' r HS HS') as [E1 [E2 [E3 [E4 [E5 E6]]]]].
    subst b' c' n' a' d' f'. exact (HP rb rc rn delta ub uc ar dr fr HC HA HD HF).
Qed.

Lemma source_proof_renaming_target_wf M r b c n f rb rc rn delta ub uc g :
  source_full_row M r -> source_sequent M b c n f r ->
  context_renaming M b c n rb rc rn delta ub uc -> numerical_renaming M f rb rc rn delta g ->
  source_sequent_wf M ub uc n g.
Proof.
  intros HR HS HC HG. apply (source_renaming_sequent_wf M b c n f rb rc rn delta ub uc g);try assumption.
  exact (source_sequent_wf_from_row M b c n f r HS (source_full_row_wellformed M r HR)).
Qed.

Lemma source_binary_renaming_graph M h a d f rb rc rn delta ar dr fr :
  sf_binary h -> sf_relation M h a d f -> numerical_renaming M a rb rc rn delta ar ->
  numerical_renaming M d rb rc rn delta dr -> numerical_renaming M f rb rc rn delta fr ->
  sf_relation M h ar dr fr.
Proof.
  intros HH HF HA HD HR.
  destruct (proj1 (numerical_renaming_binary M h a d f rb rc rn delta fr HH HF) HR) as [x [y [HX [HY HOut]]]].
  pose proof (numerical_renaming_functional M a rb rc rn delta x ar HX HA) as E. subst x.
  pose proof (numerical_renaming_functional M d rb rc rn delta y dr HY HD) as E. now subst y.
Qed.

Lemma source_quantifier_renaming_graph M universal a f rb rc rn delta rd re rm ar fr :
  sf_relation M (renaming_source_quantifier universal) a (zeroM M) f ->
  renaming_lift M rb rc rn delta rd re rm -> numerical_renaming M a rd re rm delta ar ->
  numerical_renaming M f rb rc rn delta fr ->
  sf_relation M (renaming_source_quantifier universal) ar (zeroM M) fr.
Proof.
  intros HF HL HA HR.
  destruct (sf_relation_total M (renaming_source_quantifier universal) ar (zeroM M)) as [g HG].
  assert (HGR:numerical_renaming M f rb rc rn delta g).
  { apply (proj2 (numerical_renaming_quantifier M universal a f rb rc rn delta g HF)).
    exists rd,re,rm,ar. auto. }
  pose proof (numerical_renaming_functional M f rb rc rn delta g fr HGR HR) as E. now subst g.
Qed.

Print Assumptions source_proof_renaming_definable.
Print Assumptions source_binary_renaming_graph.
Print Assumptions source_quantifier_renaming_graph.
