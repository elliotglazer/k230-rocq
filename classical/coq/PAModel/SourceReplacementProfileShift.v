(** Literal range profiles remain aligned when a fresh witness shifts all
    free parameters. The protected input/output slots are handled by an
    actual RepC/cutoff2 commuting square on arbitrary internal matrices. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  SetFormulaCodes SetSchemaConstructors SchemaConstructorBounds NumericalRenamingMaps NumericalRenaming
  NumericalSubstitutionMaps NumericalSubstitution RenamingSubstitution SourceBounded
  SourceRenamingSquare SourceFiniteCutoffShift SourceCutoffShiftCommutation
  SchemaRenamingDescriptors SourceFilteredProfileShift SourceReplacementMemberAt
  SourceOrdinalRangeMembers SourceFunctionalityShells SourcePropositionalTemplates
  SourcePropositionalRenaming SourcePropositionalRebase SourceWFSeparationConstructor SourceOrdinalMemberShell
  SourceQuantifierRules.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Lemma source_repc_tail_lookup M i :
  schema_lookup M RepC (succM M (succM M i))
    (succM M (succM M (succM M (succM M i)))).
Proof.
  assert (HX:~coding_lt M (succM M (succM M i)) (code_numeral M 2)).
  { intro H. exact (coding_not_lt_zero M i (proj1 (coding_lt_succ_cancel M i (zeroM M))
      (proj1 (coding_lt_succ_cancel M (succM M i) (code_numeral M 1)) H))). }
  apply (proj2 (schema_lookup_tail M RepC _ _ HX)).
  change (succM M (succM M (succM M (succM M i)))=
      addM M (succM M (succM M i)) (succM M (succM M (zeroM M)))).
    now rewrite Arithmetic.add_comm,!Arithmetic.add_succ,Arithmetic.add_zero.
Qed.

Theorem source_repc_cutoff_two_shift M phi matrix phi' matrix' k
    ab ac an rb rc rn :
  source_bounded M phi k -> schema_renaming M RepC phi matrix ->
  source_cutoff_shift M 2 phi phi' ->
  renaming_lift M (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1) ab ac an ->
  renaming_lift M ab ac an (code_numeral M 1) rb rc rn ->
  numerical_renaming M matrix rb rc rn (code_numeral M 1) matrix' ->
  schema_renaming M RepC phi' matrix'.
Proof.
  intros HB HRep (sb&sc&sn&HSM&HS) HL1 HL2 HR.
  pose proof (proj1 (numerical_renaming_substitution M phi (code_numeral M 4) (code_numeral M 1)
    (code_numeral M 2) (code_numeral M 2) matrix) HRep) as HSub.
  rewrite descriptor_numeral_add in HSub.
  apply (proj2 (numerical_renaming_substitution M phi' (code_numeral M 4) (code_numeral M 1)
    (code_numeral M 2) (code_numeral M 2) matrix')).
  rewrite descriptor_numeral_add.
  apply (numerical_source_renaming_square M phi k
    (code_numeral M 4) (code_numeral M 1) (code_numeral M 2) (code_numeral M 4)
    sb sc sn (code_numeral M 1) rb rc rn (code_numeral M 1)
    (code_numeral M 4) (code_numeral M 1) (code_numeral M 2) (code_numeral M 4)
    matrix phi' matrix' HB HSub
    (source_cutoff_shift_map_renaming M 2 phi phi' sb sc sn HSM HS) HR).
  intros i j l m HI HSJ HRJ HIL.
  assert (HJ:schema_lookup M RepC i j).
  { unfold schema_lookup. apply (proj2 (renaming_substitution_lookup M (code_numeral M 4)
      (code_numeral M 1) (code_numeral M 2) (code_numeral M 2) i j)).
    now rewrite descriptor_numeral_add. }
  apply (proj1 (source_cutoff_shift_map_renaming_lookup M 2 sb sc sn i l HSM)) in HIL.
  assert (HConvert:forall p q,schema_lookup M RepC p q ->
    substitution_lookup M (code_numeral M 4) (code_numeral M 1)
      (code_numeral M 2) (code_numeral M 4) p q).
  { intros p q HQ. apply (proj1 (renaming_substitution_lookup M (code_numeral M 4)
      (code_numeral M 1) (code_numeral M 2) (code_numeral M 2) p q)) in HQ.
    now rewrite descriptor_numeral_add in HQ. }
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i) as [E|[idx E]];subst i.
  - apply (proj1 (schema_lookup_first M RepC j)) in HJ. subst j.
    pose proof (substitution_lookup_functional M sb sc sn (code_numeral M 3) _ l _ HIL
      (source_cutoff_shift_map_fixed_lookup M 2 sb sc sn HSM 0)) as EL. subst l.
    apply (proj1 (renaming_lift_head M ab ac an (code_numeral M 1) rb rc rn m HL2)) in HRJ.
    subst m. apply HConvert. exact (proj2 (schema_lookup_first M RepC _) eq_refl).
  - destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) idx) as [E|[idx' E]];subst idx.
    + apply (proj1 (schema_lookup_second M RepC j)) in HJ. subst j.
      pose proof (substitution_lookup_functional M sb sc sn (code_numeral M 3) _ l _ HIL
        (source_cutoff_shift_map_fixed_lookup M 2 sb sc sn HSM 1)) as EL. subst l.
      pose proof (proj2 (proj2 HL2) (zeroM M) (zeroM M) (proj1 (proj2 HL1))) as HV.
      pose proof (renaming_lookup_functional M rb rc rn (code_numeral M 1) _ m _ HRJ HV) as EM.
      subst m. apply HConvert. exact (proj2 (schema_lookup_second M RepC _) eq_refl).
    + pose proof (renaming_lookup_functional M (code_numeral M 4) (code_numeral M 1)
        (code_numeral M 2) (code_numeral M 2) _ j _ HJ (source_repc_tail_lookup M idx')) as EJ.
      subst j.
      pose proof (substitution_lookup_functional M sb sc sn (code_numeral M 3) _ l _ HIL
        (source_cutoff_shift_map_tail_lookup M 2 sb sc sn idx' HSM)) as EL. subst l.
      pose proof (proj2 (proj2 HL2) (succM M (succM M (succM M idx')))
        (succM M (succM M (succM M (succM M idx'))))
        (proj2 (proj2 HL1) (succM M (succM M idx'))
          (succM M (succM M (succM M idx'))) (source_shift_map_lookup M _))) as HV.
      pose proof (renaming_lookup_functional M rb rc rn (code_numeral M 1) _ m _ HRJ HV) as EM.
      subst m. apply HConvert. exact (source_repc_tail_lookup M (succM M idx')).
Qed.

Definition replacement_profile_point_template :=
  SPTAnd (SPTImpl (SPTSlot 0) (SPTSlot 1)) (SPTImpl (SPTSlot 1) (SPTSlot 0)).

Theorem source_replacement_profile_at_shell M s x matrix profile :
  source_replacement_profile_at_graph M s x matrix profile ->
  exists left input body ex point,
    sf_relation M SFMember (zeroM M) (succM M s) left /\
    sf_relation M SFMember (zeroM M) (succM M (succM M x)) input /\
    sf_relation M SFAnd input matrix body /\sf_relation M SFEx body (zeroM M) ex /\
    code_relation M (schema_env3 left ex (zeroM M))
      (source_prop_expression replacement_profile_point_template) point /\
    sf_relation M SFAll point (zeroM M) profile.
Proof.
  intro HP. unfold source_replacement_profile_at_graph,E_replacement_profile_at in HP.
  destruct (schema_expression_quantifier_split M _ SFAll _ profile HP) as (point&HPoint&HAll).
  destruct (code_relation_total M (E_sf SFMember (CEconst 0) (CEadd (CEvar 0) (CEconst 1)))
    (replacement_profile_at_environment s x matrix)) as (left&HLeft).
  destruct (code_relation_total M (E_sf_ex (E_sf SFAnd
    (E_sf SFMember (CEconst 0) (CEadd (CEadd (CEvar 1) (CEconst 1)) (CEconst 1))) (CEvar 2)))
    (replacement_profile_at_environment s x matrix)) as (ex&HExCode).
  destruct (source_range_iff_split M _ _ _ left ex point HLeft HExCode HPoint)
    as (forward&reverse&HF&HR&HPointGraph).
  destruct (schema_expression_quantifier_split M _ SFEx _ ex HExCode) as (body&HBodyCode&HEx).
  destruct (schema_expression_split M _ SFAnd _ _ body HBodyCode) as (input&matrix'&HI&HM&HBody).
  change (matrix'=matrix) in HM. subst matrix'.
  exists left,input,body,ex,point. split.
  - exact (proj1 (schema_expression_graph M (replacement_profile_at_environment s x matrix)
      SFMember (CEconst 0) (CEadd (CEvar 0) (CEconst 1)) (zeroM M) (succM M s) left eq_refl
      (source_code_successor_graph M (replacement_profile_at_environment s x matrix) (CEvar 0) s eq_refl)) HLeft).
  - split.
    + exact (proj1 (schema_expression_graph M (replacement_profile_at_environment s x matrix)
        SFMember (CEconst 0) (CEadd (CEadd (CEvar 1) (CEconst 1)) (CEconst 1))
        (zeroM M) (succM M (succM M x)) input eq_refl
        (source_code_successor_graph M (replacement_profile_at_environment s x matrix)
          (CEadd (CEvar 1) (CEconst 1)) (succM M x)
          (source_code_successor_graph M (replacement_profile_at_environment s x matrix) (CEvar 1) x eq_refl))) HI).
    + split;[exact HBody|]. split;[exact HEx|]. split;[|exact HAll].
      unfold replacement_profile_point_template,source_prop_expression. functionality_graph.
Qed.

Ltac replacement_profile_code_graph :=
  match goal with
  | |- code_relation ?M ?rho (E_sf ?h ?A ?B) ?f =>
      eapply (source_sf_expression_join M rho h A B);
        [replacement_profile_code_graph|replacement_profile_code_graph|eassumption]
  | |- code_relation ?M ?rho (CEadd ?A (CEconst 1)) _ =>
      eapply (source_code_successor_graph M rho A);replacement_profile_code_graph
  | |- code_relation _ _ (CEvar _) _ => reflexivity
  | |- code_relation _ _ (CEconst _) _ => reflexivity
  end.

Theorem source_replacement_profile_at_join M s x matrix profile
    left input body ex point :
  sf_relation M SFMember (zeroM M) (succM M s) left ->
  sf_relation M SFMember (zeroM M) (succM M (succM M x)) input ->
  sf_relation M SFAnd input matrix body ->sf_relation M SFEx body (zeroM M) ex ->
  code_relation M (schema_env3 left ex (zeroM M))
    (source_prop_expression replacement_profile_point_template) point ->
  sf_relation M SFAll point (zeroM M) profile ->
  source_replacement_profile_at_graph M s x matrix profile.
Proof.
  intros HL HI HB HE HP HA.
  destruct (source_prop_template_binary M (schema_env3 left ex (zeroM M)) SFAnd
    (SPTImpl (SPTSlot 0) (SPTSlot 1)) (SPTImpl (SPTSlot 1) (SPTSlot 0)) point HP)
    as (forward&reverse&HF&HR&HPoint).
  destruct (source_prop_template_binary M _ SFImpl (SPTSlot 0) (SPTSlot 1) forward HF)
    as (l&e&HLL&HEE&HForward).
  change (l=left) in HLL. change (e=ex) in HEE. subst l e.
  destruct (source_prop_template_binary M _ SFImpl (SPTSlot 1) (SPTSlot 0) reverse HR)
    as (e&l&HEE&HLL&HReverse).
  change (l=left) in HLL. change (e=ex) in HEE. subst l e.
  unfold source_replacement_profile_at_graph,E_replacement_profile_at,E_sf_all,E_sf_ex,E_sf_iff.
  replacement_profile_code_graph.
Qed.

Theorem source_replacement_profile_shift M s x matrix profile matrix' profile'
    ab ac an rb rc rn :
  source_replacement_profile_at_graph M s x matrix profile ->
  renaming_lift M (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1) ab ac an ->
  renaming_lift M ab ac an (code_numeral M 1) rb rc rn ->
  numerical_renaming M matrix rb rc rn (code_numeral M 1) matrix' ->
  source_replacement_profile_at_graph M (succM M s) (succM M x) matrix' profile' ->
  source_formula_shift M profile profile'.
Proof.
  intros HP HL1 HL2 HR HP'.
  destruct (source_replacement_profile_at_shell M s x matrix profile HP)
    as (left&input&body&ex&point&HLeft&HInput&HBody&HEx&HPoint&HAll).
  destruct (source_replacement_profile_at_shell M (succM M s) (succM M x) matrix' profile' HP')
    as (left'&input'&body'&ex'&point'&HLeft'&HInput'&HBody'&HEx'&HPoint'&HAll').
  assert (RL:numerical_renaming M left ab ac an (code_numeral M 1) left').
  { apply (proj2 (numerical_renaming_member M _ _ left _ _ _ _ left' HLeft)).
    exists (zeroM M),(succM M (succM M s)). split;[exact (proj1 (proj2 HL1))|].
    split;[|exact HLeft']. exact (proj2 (proj2 HL1) s (succM M s) (source_shift_map_lookup M s)). }
  assert (RI:numerical_renaming M input rb rc rn (code_numeral M 1) input').
  { apply (proj2 (numerical_renaming_member M _ _ input _ _ _ _ input' HInput)).
    exists (zeroM M),(succM M (succM M (succM M x))). split;[exact (proj1 (proj2 HL2))|].
    split;[|exact HInput']. exact (proj2 (proj2 HL2) (succM M x) (succM M (succM M x))
      (proj2 (proj2 HL1) x (succM M x) (source_shift_map_lookup M x))). }
  assert (RB:numerical_renaming M body rb rc rn (code_numeral M 1) body').
  { apply (proj2 (numerical_renaming_binary M SFAnd input matrix body _ _ _ _ body'
      (or_introl eq_refl) HBody)). exists input',matrix'. auto. }
  assert (RE:numerical_renaming M ex ab ac an (code_numeral M 1) ex').
  { apply (proj2 (numerical_renaming_quantifier M false body ex _ _ _ _ ex' HEx)).
    exists rb,rc,rn,body'. auto. }
  assert (RP:numerical_renaming M point ab ac an (code_numeral M 1) point').
  { apply (source_prop_expression_renaming M (schema_env3 left ex (zeroM M))
      (schema_env3 left' ex' (zeroM M)) ab ac an (code_numeral M 1)
      replacement_profile_point_template point point');[|exact HPoint|exact HPoint'].
    intros [|[|i]];cbn [schema_env3];try assumption.
    exact (proj2 (numerical_renaming_invalid M (zeroM M) ab ac an (code_numeral M 1)
      (zeroM M) (or_introl eq_refl)) eq_refl). }
  apply (proj2 (numerical_renaming_quantifier M true point profile _ _ _ _ profile' HAll)).
  exists ab,ac,an,point'. auto.
Qed.

Print Assumptions source_repc_cutoff_two_shift.
Print Assumptions source_replacement_profile_at_shell.
Print Assumptions source_replacement_profile_at_join.
Print Assumptions source_replacement_profile_shift.
