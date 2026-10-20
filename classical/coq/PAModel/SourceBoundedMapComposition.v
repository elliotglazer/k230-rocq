(** Packing composed variable actions only on the required internal bound.
    PA bounded collection supplies the range bound before beta packing. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension BetaPacking BoundedCollection
  CodeExpressions NumericalProofs NumericalEnvironments NumericalSubstitutionMaps NumericalSubstitution
  SourceBounded SourceSubstitutionBounds SourceSubstitutionComposition
  NumericalRenaming RenamingSubstitution SourceRenamingIdentity SourceShiftSpecialization.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Lemma beta_pack_total_function M rho theta n :
  (forall i,coding_lt M i n ->exists v,holds M (v .: i .: rho) theta) ->
  (forall i v w,coding_lt M i n ->holds M (v .: i .: rho) theta ->
    holds M (w .: i .: rho) theta ->v=w) ->
  exists b c,forall i v,coding_lt M i n ->
    (beta M b c i v <->holds M (v .: i .: rho) theta).
Proof.
  intros HT HU. destruct (bounded_collection M theta rho n HT) as (bound&HB).
  apply (beta_pack_function M rho theta n bound HT);[|exact HU].
  intros i v HI HV. destruct (HB i HI) as (w&HW&HF).
  pose proof (HU i v w HI HV HF) as E. subst v.
  exact (coding_lt_trans M w bound (succM M bound) HW (coding_lt_succ M bound)).
Qed.

Definition composed_substitution_lookup M ab ac an abase rb rc rn rbase i v :=
  exists j,substitution_lookup M ab ac an abase i j /\substitution_lookup M rb rc rn rbase j v.
Definition composed_substitution_lookup_formula (ab ac an abase rb rc rn rbase i v:term) :form :=
  ∃(substitution_lookup_formula ab`[↑] ac`[↑] an`[↑] abase`[↑] i`[↑] $0 ∧
    substitution_lookup_formula rb`[↑] rc`[↑] rn`[↑] rbase`[↑] $0 v`[↑]).
Local Opaque holds substitution_lookup_formula.
Lemma composed_substitution_lookup_formula_correct M rho ab ac an abase rb rc rn rbase i v :
  holds M rho (composed_substitution_lookup_formula ab ac an abase rb rc rn rbase i v) <->
  composed_substitution_lookup M (evalM M rho ab)(evalM M rho ac)(evalM M rho an)(evalM M rho abase)
    (evalM M rho rb)(evalM M rho rc)(evalM M rho rn)(evalM M rho rbase)(evalM M rho i)(evalM M rho v).
Proof.
  unfold composed_substitution_lookup_formula,composed_substitution_lookup.
  rewrite holds_ex. setoid_rewrite holds_and. setoid_rewrite substitution_lookup_formula_correct.
  repeat setoid_rewrite substitution_eval_up. reflexivity.
Qed.

Theorem bounded_substitution_composition_map M ab ac an abase rb rc rn rbase k :
  exists cb cc,forall i v,coding_lt M i k ->
    (substitution_lookup M cb cc k (zeroM M) i v <->
      composed_substitution_lookup M ab ac an abase rb rc rn rbase i v).
Proof.
  set (rho:=rbase .: rn .: rc .: rb .: abase .: an .: ac .: ab .: fun _=>zeroM M).
  set (F:=composed_substitution_lookup_formula $9 $8 $7 $6 $5 $4 $3 $2 $1 $0).
  assert (HF:forall i v,holds M (v .: i .: rho) F <->
      composed_substitution_lookup M ab ac an abase rb rc rn rbase i v).
  { intros i v. unfold F,rho. apply composed_substitution_lookup_formula_correct. }
  assert (HT:forall i,coding_lt M i k ->exists v,holds M (v .: i .: rho) F).
  { intros i _. destruct (substitution_lookup_total M ab ac an abase i) as (j&HJ).
    destruct (substitution_lookup_total M rb rc rn rbase j) as (v&HV).
    exists v. apply HF. exists j. auto. }
  assert (HU:forall i v w,coding_lt M i k ->holds M (v .: i .: rho) F ->
      holds M (w .: i .: rho) F ->v=w).
  { intros i v w _ HV HW. apply HF in HV,HW. destruct HV as (j&HJ&HV),HW as (j'&HJ'&HW).
    pose proof (substitution_lookup_functional M ab ac an abase i j j' HJ HJ') as E. subst j'.
    exact (substitution_lookup_functional M rb rc rn rbase j v w HV HW). }
  destruct (beta_pack_total_function M rho F k HT HU) as (cb&cc&HBC).
  exists cb,cc. intros i v HI. rewrite (substitution_lookup_inside M cb cc k (zeroM M) i v HI).
  rewrite (HBC i v HI). apply HF.
Qed.

Theorem numerical_substitution_composition_total M f k ab ac an abase rb rc rn rbase g h :
  source_bounded M f k ->numerical_substitution M f ab ac an abase g ->
  numerical_substitution M g rb rc rn rbase h ->exists cb cc,
    numerical_substitution M f cb cc k (zeroM M) h /\
    forall i v,coding_lt M i k ->
      (substitution_lookup M cb cc k (zeroM M) i v <->
        composed_substitution_lookup M ab ac an abase rb rc rn rbase i v).
Proof.
  intros HF HA HR. destruct (bounded_substitution_composition_map M ab ac an abase rb rc rn rbase k)
    as (cb&cc&HC). exists cb,cc. split;[|exact HC].
  apply (numerical_substitution_composition M f k ab ac an abase rb rc rn rbase cb cc k (zeroM M) g h HF HA HR).
  intros i j v HI HJ HV. apply (proj2 (HC i v HI)). exists j. auto.
Qed.

Theorem numerical_prefix_substitution_compare M f k cb cc out rb rc rn rbase :
  source_bounded M f k ->numerical_substitution M f cb cc k (zeroM M) out ->
  (forall i v,coding_lt M i k ->substitution_lookup M cb cc k (zeroM M) i v ->
    substitution_lookup M rb rc rn rbase i v) ->
  numerical_substitution M f rb rc rn rbase out.
Proof.
  intros HF HC HA.
  assert (HOut:source_bounded M out (succM M cb)).
  { apply (numerical_substitution_preserves_bound M f cb cc k (zeroM M) out k _ HF HC).
    intros i j HI HJ. apply (proj1 (substitution_lookup_inside M cb cc k (zeroM M) i j HI)) in HJ.
    exact (remainder_le_dividend M cb (beta_modulus M cc i) j HJ). }
  assert (HId:numerical_substitution M out (zeroM M)(zeroM M)(zeroM M)(zeroM M) out).
  { apply (proj1 (numerical_renaming_empty_substitution M out _ _ _ out)).
    apply (numerical_renaming_identity_on_bound M out _ _ _ _ _ HOut).
    intros i _. apply source_empty_renaming_lookup. }
  apply (numerical_substitution_composition M f k cb cc k (zeroM M)
    (zeroM M)(zeroM M)(zeroM M)(zeroM M) rb rc rn rbase out out HF HC HId).
  intros i j v HI HJ HV.
  pose proof (substitution_lookup_functional M _ _ _ _ j v j HV (source_empty_substitution_lookup M j)) as E.
  subst v. exact (HA i j HI HJ).
Qed.

Print Assumptions bounded_substitution_composition_map.
Print Assumptions numerical_substitution_composition_total.
Print Assumptions numerical_prefix_substitution_compare.
