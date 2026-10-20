(** Exact cross-specialization of the two minimality exclusions used by
    Replacement functionality. All predicate codes and bounds are internal. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SourceBounded
  NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation NumericalRenamingMaps
  NumericalRenaming RenamingSubstitution SourceBoundedMapComposition SourceFiniteCutoffShift
  SourceCutoffShiftCommutation SourceFixedSwap SourceSwap SchemaRenamingDescriptors SubstitutionSource.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Lemma numerical_three_substitutions_compare M f k
    ab ac an abase bb bc bn bbase cb cc cn cbase tb tc tn tbase f1 f2 out :
  source_bounded M f k ->numerical_substitution M f ab ac an abase f1 ->
  numerical_substitution M f1 bb bc bn bbase f2 ->numerical_substitution M f2 cb cc cn cbase out ->
  (forall i j1 j2 v,coding_lt M i k ->substitution_lookup M ab ac an abase i j1 ->
    substitution_lookup M bb bc bn bbase j1 j2 ->substitution_lookup M cb cc cn cbase j2 v ->
    substitution_lookup M tb tc tn tbase i v) ->numerical_substitution M f tb tc tn tbase out.
Proof.
  intros HB H1 H2 H3 HP.
  destruct (numerical_substitution_composition_total M f k ab ac an abase bb bc bn bbase f1 f2 HB H1 H2)
    as (p&q&HS&HPS).
  destruct (numerical_substitution_composition_total M f k p q k (zeroM M) cb cc cn cbase f2 out HB HS H3)
    as (r&s&HT&HRT).
  apply (numerical_prefix_substitution_compare M f k r s out tb tc tn tbase HB HT).
  intros i v HI HV. apply (proj1 (HRT i v HI)) in HV. destruct HV as (j2&HJ2&H3').
  apply (proj1 (HPS i j2 HI)) in HJ2. destruct HJ2 as (j1&H1'&H2').
  exact (HP i j1 j2 v HI H1' H2' H3').
Qed.

Definition oc_side_dividend (side:bool) := if side then 22 else 14.
Definition oc_cross_term M (side:bool) := code_numeral M (if side then 0 else 1).
Definition oc_side_renaming M side f g := numerical_renaming M f
  (code_numeral M (oc_side_dividend side)) (code_numeral M 3) (code_numeral M 2) (code_numeral M 1) g.

Lemma oc_side_first_lookup M side :renaming_lookup M (code_numeral M (oc_side_dividend side))
  (code_numeral M 3) (code_numeral M 2) (code_numeral M 1) (zeroM M) (code_numeral M 2).
Proof.
  destruct side;[change (schema_lookup M RepA (zeroM M) (code_numeral M 2))|
    change (schema_lookup M RepB (zeroM M) (code_numeral M 2))];
    apply (proj2 (schema_lookup_first M _ _));reflexivity.
Qed.
Lemma oc_cross_second_lookup M side :renaming_lookup M (code_numeral M (oc_side_dividend (negb side)))
  (code_numeral M 3) (code_numeral M 2) (code_numeral M 1) (code_numeral M 1) (oc_cross_term M side).
Proof.
  destruct side;[change (schema_lookup M RepB (code_numeral M 1) (code_numeral M 0))|
    change (schema_lookup M RepA (code_numeral M 1) (code_numeral M 1))];
    apply (proj2 (schema_lookup_second M _ _));reflexivity.
Qed.
Lemma oc_side_tail_lookup M side idx :renaming_lookup M (code_numeral M (oc_side_dividend side))
  (code_numeral M 3) (code_numeral M 2) (code_numeral M 1)
  (succM M (succM M idx)) (succM M (succM M (succM M idx))).
Proof.
  assert (HN:~coding_lt M (succM M (succM M idx)) (code_numeral M 2)).
  { intro HI. exact (coding_not_lt_zero M idx
      (proj1 (coding_lt_succ_cancel M idx (zeroM M))
        (proj1 (coding_lt_succ_cancel M (succM M idx) (succM M (zeroM M))) HI))). }
  apply (proj2 (renaming_lookup_outside M _ _ _ _ _ _ HN)).
  exact (Arithmetic.succ_as_add M (succM M (succM M idx))).
Qed.

Theorem source_oc_cross_instantiation M side phi k swapped shifted matrix other cb cc cn rb rc rn :
  source_bounded M phi k ->
  numerical_renaming M phi (code_numeral M 3) (code_numeral M 1) (code_numeral M 2) (zeroM M) swapped ->
  source_cutoff_shift_map M 2 cb cc cn ->numerical_substitution M phi cb cc cn (code_numeral M 3) shifted ->
  renaming_lift M (code_numeral M (oc_side_dividend side)) (code_numeral M 3)
    (code_numeral M 2) (code_numeral M 1) rb rc rn ->
  numerical_renaming M shifted rb rc rn (code_numeral M 1) matrix ->
  oc_side_renaming M (negb side) swapped other ->
  numerical_instantiation M matrix (oc_cross_term M side) other.
Proof.
  intros HB HSwap HM HS HL HR HOther.
  pose proof (proj1 (numerical_renaming_substitution M phi _ _ _ _ swapped) HSwap) as HSwapS.
  pose proof (proj1 (numerical_renaming_substitution M swapped _ _ _ _ other) HOther) as HOtherS.
  destruct (numerical_substitution_composition_total M phi k
    (code_numeral M 3) (code_numeral M 1) (code_numeral M 2) (addM M (code_numeral M 2) (zeroM M))
    (code_numeral M (oc_side_dividend (negb side))) (code_numeral M 3)
      (code_numeral M 2) (addM M (code_numeral M 2) (code_numeral M 1))
    swapped other HB HSwapS HOtherS) as (tb&tc&HTarget&HTargetLookup).
  destruct (numerical_instantiation_total M matrix (oc_cross_term M side)) as (result&HI).
  destruct HI as (ib&ic&HHead&HResult).
  assert (HCompared:numerical_substitution M phi tb tc k (zeroM M) result).
  { apply (numerical_three_substitutions_compare M phi k cb cc cn (code_numeral M 3)
      rb rc rn (addM M rn (code_numeral M 1)) ib ic (code_numeral M 1) (zeroM M)
      tb tc k (zeroM M) shifted matrix result HB HS
      (proj1 (numerical_renaming_substitution M shifted rb rc rn (code_numeral M 1) matrix) HR) HResult).
    intros i j1 j2 v HI H1 H2 H3.
    apply (proj2 (HTargetLookup i v HI)).
    apply (proj2 (renaming_substitution_lookup M rb rc rn (code_numeral M 1) j1 j2)) in H2.
    destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) i) as [E|[idx E]];subst i.
    - assert (E1:j1=zeroM M).
      { exact (substitution_lookup_functional M cb cc cn _ _ j1 _ H1
          (source_cutoff_shift_map_fixed_lookup M 2 cb cc cn HM 0)). }
      subst j1. apply (proj1 (renaming_lift_head M _ _ _ _ rb rc rn j2 HL)) in H2. subst j2.
      pose proof (substitution_lookup_functional M ib ic _ _ _ v _ H3 HHead) as EV. subst v.
      exists (code_numeral M 1). split.
      + exact (proj1 (renaming_substitution_lookup M _ _ _ _ _ _) (proj1 (source_fixed_swap_map M))).
      + exact (proj1 (renaming_substitution_lookup M _ _ _ _ _ _) (oc_cross_second_lookup M side)).
    - destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
        (fun ax H rho=>axioms M ax rho H) idx) as [E|[tail E]];subst idx.
      + assert (E1:j1=code_numeral M 1).
        { exact (substitution_lookup_functional M cb cc cn _ _ j1 _ H1
            (source_cutoff_shift_map_fixed_lookup M 2 cb cc cn HM 1)). }
        subst j1.
        assert (H2':renaming_lookup M rb rc rn (code_numeral M 1) (code_numeral M 1) (code_numeral M 3)).
        { exact (proj2 (proj2 HL) (zeroM M) (code_numeral M 2) (oc_side_first_lookup M side)). }
        pose proof (renaming_lookup_functional M rb rc rn _ _ j2 _ H2 H2') as E2. subst j2.
        pose proof (substitution_lookup_functional M ib ic _ _ _ v _ H3
          (substitution_singleton_tail M ib ic (code_numeral M 2))) as EV. subst v.
        exists (zeroM M). split.
        * exact (proj1 (renaming_substitution_lookup M _ _ _ _ _ _) (proj2 (source_fixed_swap_map M))).
        * exact (proj1 (renaming_substitution_lookup M _ _ _ _ _ _) (oc_side_first_lookup M (negb side))).
      + assert (E1:j1=succM M (succM M (succM M tail))).
        { exact (substitution_lookup_functional M cb cc cn _ _ j1 _ H1
            (source_cutoff_shift_map_tail_lookup M 2 cb cc cn tail HM)). }
        subst j1.
        assert (H2':renaming_lookup M rb rc rn (code_numeral M 1)
          (succM M (succM M (succM M tail))) (succM M (succM M (succM M (succM M tail))))).
        { exact (proj2 (proj2 HL) (succM M (succM M tail)) (succM M (succM M (succM M tail)))
            (oc_side_tail_lookup M side tail)). }
        pose proof (renaming_lookup_functional M rb rc rn _ _ j2 _ H2 H2') as E2. subst j2.
        pose proof (substitution_lookup_functional M ib ic _ _ _ v _ H3
          (substitution_singleton_tail M ib ic (succM M (succM M (succM M tail))))) as EV. subst v.
        exists (succM M (succM M tail)). split.
        * exact (proj1 (renaming_substitution_lookup M _ _ _ _ _ _) (source_swap_tail M _ _ tail)).
        * exact (proj1 (renaming_substitution_lookup M _ _ _ _ _ _) (oc_side_tail_lookup M (negb side) tail)). }
  pose proof (numerical_substitution_functional M phi tb tc k (zeroM M) result other HCompared HTarget) as E.
  subst result. exists ib,ic. split;assumption.
Qed.

Print Assumptions source_oc_cross_instantiation.
