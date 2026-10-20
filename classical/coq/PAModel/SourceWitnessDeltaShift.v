(** Witness closure is stable under a source variable shift, with its
    container name and parameter tail both incremented. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  SetFormulaCodes SetSchemaConstructors SourceBounded SourceUpperWitnessRecipes SourceWitnessMatrixSpecialization
  SourceTraceMatrixAlignment SourceFiniteCutoffShift SourceSubstitutionComposition
  NumericalRenamingMaps NumericalRenaming NumericalSubstitutionMaps NumericalSubstitution
  RenamingSubstitution NumericalContextRenaming SourceQuantifierRules.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Theorem source_identity_cutoff_two_increment M phi f g delta k :
  source_bounded M phi k ->
  numerical_renaming M phi (code_numeral M 4) (code_numeral M 1)
    (code_numeral M 2) delta f ->source_cutoff_shift M 2 f g ->
  numerical_renaming M phi (code_numeral M 4) (code_numeral M 1)
    (code_numeral M 2) (succM M delta) g.
Proof.
  intros HP HR [b [c [n [HM HG]]]].
  apply (proj2 (numerical_renaming_substitution M phi (code_numeral M 4)
    (code_numeral M 1) (code_numeral M 2) (succM M delta) g)).
  apply (numerical_substitution_composition M phi k
    (code_numeral M 4) (code_numeral M 1) (code_numeral M 2)
    (addM M (code_numeral M 2) delta) b c n (code_numeral M 3)
    (code_numeral M 4) (code_numeral M 1) (code_numeral M 2)
    (addM M (code_numeral M 2) (succM M delta)) f g HP
    (proj1 (numerical_renaming_substitution M phi _ _ _ delta f) HR) HG).
  intros i j v _ HFirst HSecond.
  apply (proj2 (renaming_substitution_lookup M (code_numeral M 4) (code_numeral M 1)
    (code_numeral M 2) delta i j)) in HFirst.
  apply (proj1 (renaming_substitution_lookup M (code_numeral M 4) (code_numeral M 1)
    (code_numeral M 2) (succM M delta) i v)).
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i) as [->|[i' ->]].
  - pose proof (renaming_lookup_functional M _ _ _ _ _ j _ HFirst
      (proj1 (source_identity_delta_prefix M delta))) as E. subst j.
    pose proof (substitution_lookup_functional M b c n (code_numeral M 3)
      (zeroM M) v (zeroM M) HSecond (source_cutoff_shift_map_fixed_lookup M 2 b c n HM 0)) as E.
    subst v. exact (proj1 (source_identity_delta_prefix M (succM M delta))).
  - destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) i') as [->|[i'' ->]].
    + pose proof (renaming_lookup_functional M _ _ _ _ _ j _ HFirst
        (proj2 (source_identity_delta_prefix M delta))) as E. subst j.
      pose proof (substitution_lookup_functional M b c n (code_numeral M 3)
        (code_numeral M 1) v (code_numeral M 1) HSecond
        (source_cutoff_shift_map_fixed_lookup M 2 b c n HM 1)) as E.
      subst v. exact (proj2 (source_identity_delta_prefix M (succM M delta))).
    + apply (proj1 (renaming_lookup_outside M _ _ _ _ _ _ (source_two_succ_not_lt_two M i''))) in HFirst.
      rewrite !Arithmetic.add_succ in HFirst. subst j.
      pose proof (substitution_lookup_functional M b c n (code_numeral M 3) _ v _ HSecond
        (source_cutoff_shift_map_tail M 2 b c n (addM M i'' delta) HM)) as E. subst v.
      apply (proj2 (renaming_lookup_outside M _ _ _ _ _ _ (source_two_succ_not_lt_two M i''))).
      cbn [source_succ_iter]. rewrite !Arithmetic.add_succ.
      rewrite (Arithmetic.add_comm M i'' (succM M delta)),Arithmetic.add_succ,
        (Arithmetic.add_comm M delta i''). reflexivity.
Qed.

Theorem source_two_lifted_shift_cutoff M rb rc rn sb sc sn :
  renaming_lift M (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1) rb rc rn ->
  renaming_lift M rb rc rn (code_numeral M 1) sb sc sn ->source_cutoff_shift_map M 2 sb sc sn.
Proof.
  intros HL1 HL2. exists rb,rc,rn. split.
  - exists (zeroM M),(zeroM M),(zeroM M). split;[repeat split;reflexivity|].
    pose proof (proj1 (renaming_substitution_lift M (zeroM M) (zeroM M) (zeroM M)
      (code_numeral M 1) rb rc rn) HL1) as H. now rewrite Arithmetic.add_zero in H.
  - pose proof (proj1 (renaming_substitution_lift M rb rc rn (code_numeral M 1) sb sc sn) HL2) as H.
    rewrite (proj1 HL1) in H |- *. cbn [code_numeral] in H.
    now rewrite Arithmetic.add_succ,Arithmetic.add_zero in H.
Qed.

Theorem source_upper_witness_closed_shift_total M phi k delta b closed :
  source_bounded M phi k ->source_upper_witness_closed_recipe M phi delta b closed ->
  exists shifted,source_upper_witness_closed_recipe M phi (succM M delta) (succM M b) shifted /\
    source_formula_shift M closed shifted.
Proof.
  intros HP [mat [HM HCode]].
  destruct (source_upper_witness_closed_shell M mat b closed HCode)
    as (guard & member & pair & some & bounded & request & point & HG & HMem & HPair & HS & HB & HR & HI & HA).
  destruct (renaming_lift_total M (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1))
    as [rb [rc [rn HL1]]].
  destruct (renaming_lift_total M rb rc rn (code_numeral M 1)) as [sb [sc [sn HL2]]].
  destruct (numerical_renaming_total M mat sb sc sn (code_numeral M 1)) as [mat' HMatShift].
  assert (HMatCut:source_cutoff_shift M 2 mat mat').
  { exists sb,sc,sn. split;[exact (source_two_lifted_shift_cutoff M rb rc rn sb sc sn HL1 HL2)|].
    pose proof (proj1 (numerical_renaming_substitution M mat sb sc sn (code_numeral M 1) mat') HMatShift) as H.
    rewrite (proj1 HL2),(proj1 HL1) in H |- *. cbn [code_numeral] in H.
    now rewrite !Arithmetic.add_succ,Arithmetic.add_zero in H. }
  pose proof (source_identity_cutoff_two_increment M phi mat mat' delta k HP HM HMatCut) as HM'.
  destruct (code_relation_total M (E_upper_witness_closed (CEvar 0) (CEvar 1))
    (schema_env3 mat' (succM M b) (succM M b))) as [shifted HCode'].
  destruct (source_upper_witness_closed_shell M mat' (succM M b) shifted HCode')
    as (guard' & member' & pair' & some' & bounded' & request' & point' & HG' & HMem' & HPair' & HS' & HB' & HR' & HI' & HA').
  assert (RGuard:numerical_renaming M guard rb rc rn (code_numeral M 1) guard').
  { apply (proj2 (numerical_renaming_member M _ _ _ rb rc rn (code_numeral M 1) guard' HG)).
    exists (zeroM M),(succM M (succM M b)). split.
    - exact (proj2 (renaming_lift_head M _ _ _ _ rb rc rn (zeroM M) HL1) eq_refl).
    - split;[|exact HG']. apply (proj2 (renaming_lift_tail M _ _ _ _ rb rc rn b (succM M b) HL1)).
      apply context_shift_lookup. reflexivity. }
  assert (RMember:numerical_renaming M member sb sc sn (code_numeral M 1) member').
  { apply (proj2 (numerical_renaming_member M _ _ _ sb sc sn (code_numeral M 1) member' HMem)).
    exists (zeroM M),(succM M (succM M (succM M b))). split.
    - exact (proj2 (renaming_lift_head M _ _ _ _ sb sc sn (zeroM M) HL2) eq_refl).
    - split;[|exact HMem']. apply (proj2 (renaming_lift_tail M _ _ _ _ sb sc sn
        (succM M b) (succM M (succM M b)) HL2)).
      apply (proj2 (renaming_lift_tail M _ _ _ _ rb rc rn b (succM M b) HL1)).
      apply context_shift_lookup. reflexivity. }
  assert (RPair:numerical_renaming M pair sb sc sn (code_numeral M 1) pair').
  { apply (proj2 (numerical_renaming_binary M SFAnd member mat pair sb sc sn
      (code_numeral M 1) pair' (or_introl eq_refl) HPair)).
    exists member',mat'. auto. }
  assert (RSome:numerical_renaming M some rb rc rn (code_numeral M 1) some').
  { apply (proj2 (numerical_renaming_quantifier M false mat some rb rc rn (code_numeral M 1) some' HS)).
    exists sb,sc,sn,mat'. auto. }
  assert (RBound:numerical_renaming M bounded rb rc rn (code_numeral M 1) bounded').
  { apply (proj2 (numerical_renaming_quantifier M false pair bounded rb rc rn (code_numeral M 1) bounded' HB)).
    exists sb,sc,sn,pair'. auto. }
  assert (RRequest:numerical_renaming M request rb rc rn (code_numeral M 1) request').
  { apply (proj2 (numerical_renaming_binary M SFImpl some bounded request rb rc rn
      (code_numeral M 1) request' (or_intror (or_intror eq_refl)) HR)).
    exists some',bounded'. auto. }
  assert (RPoint:numerical_renaming M point rb rc rn (code_numeral M 1) point').
  { apply (proj2 (numerical_renaming_binary M SFImpl guard request point rb rc rn
      (code_numeral M 1) point' (or_intror (or_intror eq_refl)) HI)).
    exists guard',request'. auto. }
  exists shifted. split;[exists mat';auto|].
  apply (proj2 (numerical_renaming_quantifier M true point closed (zeroM M) (zeroM M)
    (zeroM M) (code_numeral M 1) shifted HA)).
  exists rb,rc,rn,point'. auto.
Qed.

Print Assumptions source_identity_cutoff_two_increment.
Print Assumptions source_two_lifted_shift_cutoff.
Print Assumptions source_upper_witness_closed_shift_total.
