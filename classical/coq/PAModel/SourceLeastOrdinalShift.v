(** Moving the canonical least-ordinal goal under one eigenvariable
    commutes with its two witness binders, for arbitrary internal matrices. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
  SetSchemaConstructors SourceBounded SourceSubstitutionIdentity NumericalSubstitutionMaps
  NumericalSubstitution NumericalRenaming RenamingSubstitution SourceQuantifierRules
  SourceFiniteCutoffShift SourceQfFunctionality SourceOrdinalPredicate SourceLeastOrdinalGoal
  SourcePropositionalRebase SourceWFSeparationConstructor SourceCutoffShiftCommutation.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Local Opaque source_ordinal_predicate source_ordinal_predicate_code.

Lemma source_least_ordinal_expression_split M phi inserted least :
  code_relation M (sf_env phi inserted) least_ordinal_expression least ->
  exists body tag allpoint point neg mem,
    sf_relation M SFEx body (zeroM M) least /\
    sf_relation M SFAnd tag allpoint body /\
    sf_relation M SFAnd (source_ordinal_predicate_code M) phi tag /\
    sf_relation M SFAll point (zeroM M) allpoint /\
    sf_relation M SFImpl mem neg point /\
    sf_relation M SFMember (code_numeral M 0) (code_numeral M 1) mem /\
    sf_relation M SFImpl inserted (zeroM M) neg.
Proof.
  intro HG. unfold least_ordinal_expression,E_sf_ex,E_sf_all in HG.
  destruct (schema_expression_quantifier_split M _ SFEx _ least HG) as (body&HB&HE).
  destruct (schema_expression_split M _ SFAnd _ _ body HB) as (tag&allpoint&HT&HA&HBody).
  destruct (schema_expression_split M _ SFAnd _ _ tag HT) as (ordinal&matrix&HO&HM&HTag).
  change (ordinal=source_ordinal_predicate_code M) in HO. change (matrix=phi) in HM.
  subst ordinal matrix.
  destruct (schema_expression_quantifier_split M _ SFAll _ allpoint HA) as (point&HP&HAll).
  destruct (schema_expression_split M _ SFImpl _ _ point HP) as (mem&neg&HMem&HN&HPoint).
  unfold E_sf_mem in HMem.
  destruct (schema_expression_split M _ SFMember _ _ mem HMem) as (z&o&HZ&HOne&HMember).
  change (z=code_numeral M 0) in HZ. change (o=code_numeral M 1) in HOne. subst z o.
  destruct (schema_expression_split M _ SFImpl _ _ neg HN) as (p&f&HPhi&HF&HNeg).
  change (p=inserted) in HPhi. change (f=zeroM M) in HF. subst p f.
  exists body,tag,allpoint,point,neg,mem. repeat split;assumption.
Qed.

Theorem source_least_ordinal_shift M phi phi' least least' k :
  source_bounded M phi k -> source_cutoff_shift M 1 phi phi' ->
  source_least_ordinal_graph M phi least -> source_formula_shift M least least' ->
  source_least_ordinal_graph M phi' least'.
Proof.
  intros HB HPhi (inserted&HInserted&HGraph) HShift.
  destruct (substitution_lift_total M (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1))
    as (d&e&j&HL1).
  assert (HM1:source_cutoff_shift_map M 1 d e j).
  { exists (zeroM M),(zeroM M),(zeroM M). split;[repeat split;reflexivity|exact HL1]. }
  destruct (substitution_lift_total M d e j (code_numeral M 2)) as (v&w&l&HL2).
  assert (HM2:source_cutoff_shift_map M 2 v w l).
  { exists d,e,j. split;assumption. }
  destruct (numerical_substitution_total M inserted v w l (code_numeral M 3)) as (q&HQ).
  assert (HC2:source_cutoff_shift M 2 inserted q) by (exists v,w,l;auto).
  pose proof (source_cutoff_one_two_commute M phi inserted phi' q k HB HInserted HPhi HC2) as HNewInserted.
  destruct (code_relation_total M least_ordinal_expression (sf_env phi' q)) as (target&HTarget).
  assert (SPhi:numerical_substitution M phi d e j (code_numeral M 2) phi').
  { destruct HPhi as (pb&pc&pn&HPM&HPS).
    apply (proj1 (numerical_substitution_extensional M phi pb pc pn d e j (code_numeral M 2) phi'
      (source_cutoff_shift_maps_equivalent M 1 pb pc pn d e j HPM HM1))). exact HPS. }
  assert (SOrd:numerical_substitution M (source_ordinal_predicate_code M) d e j (code_numeral M 2)
    (source_ordinal_predicate_code M)).
  { apply (numerical_substitution_identity_on_bound M _ d e j (code_numeral M 2) (code_numeral M 1)
      (source_ordinal_predicate_bounded M)).
    intros i HI. destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) i) as [E|[idx E]];subst i.
    - exact (source_cutoff_shift_map_fixed_lookup M 1 d e j HM1 0).
    - exfalso. exact (coding_not_lt_zero M idx (proj1 (coding_lt_succ_cancel M idx (zeroM M)) HI)). }
  destruct (source_least_ordinal_expression_split M phi inserted least HGraph)
    as (body&tag&allpoint&point&neg&mem&HEx&HBody&HTag&HAll&HPoint&HMem&HNeg).
  destruct (source_least_ordinal_expression_split M phi' q target HTarget)
    as (body'&tag'&allpoint'&point'&neg'&mem'&HEx'&HBody'&HTag'&HAll'&HPoint'&HMem'&HNeg').
  assert (SMem:numerical_substitution M mem v w l (code_numeral M 3) mem').
  { apply (proj2 (numerical_substitution_member M _ _ mem v w l _ mem' HMem)).
    exists (code_numeral M 0),(code_numeral M 1). split.
    - exact (source_cutoff_shift_map_fixed_lookup M 2 v w l HM2 0).
    - split;[exact (source_cutoff_shift_map_fixed_lookup M 2 v w l HM2 1)|exact HMem']. }
  assert (SFalse:numerical_substitution M (zeroM M) v w l (code_numeral M 3) (zeroM M)).
  { apply (proj2 (numerical_substitution_invalid M (zeroM M) v w l _ _ (or_introl eq_refl))). reflexivity. }
  assert (SNeg:numerical_substitution M neg v w l (code_numeral M 3) neg').
  { apply (proj2 (numerical_substitution_binary M SFImpl inserted (zeroM M) neg v w l _ neg'
      (or_intror (or_intror eq_refl)) HNeg)). exists q,(zeroM M). repeat split;assumption. }
  assert (SPoint:numerical_substitution M point v w l (code_numeral M 3) point').
  { apply (proj2 (numerical_substitution_binary M SFImpl mem neg point v w l _ point'
      (or_intror (or_intror eq_refl)) HPoint)). exists mem',neg'. repeat split;assumption. }
  assert (SAll:numerical_substitution M allpoint d e j (code_numeral M 2) allpoint').
  { apply (proj2 (numerical_substitution_quantifier M true point allpoint d e j _ allpoint' HAll)).
    exists v,w,l,point'. split;[exact HL2|]. split;assumption. }
  assert (STag:numerical_substitution M tag d e j (code_numeral M 2) tag').
  { apply (proj2 (numerical_substitution_binary M SFAnd _ _ tag d e j _ tag' (or_introl eq_refl) HTag)).
    exists (source_ordinal_predicate_code M),phi'. repeat split;assumption. }
  assert (SBody:numerical_substitution M body d e j (code_numeral M 2) body').
  { apply (proj2 (numerical_substitution_binary M SFAnd tag allpoint body d e j _ body' (or_introl eq_refl) HBody)).
    exists tag',allpoint'. repeat split;assumption. }
  assert (STarget:numerical_substitution M least (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1) target).
  { apply (proj2 (numerical_substitution_quantifier M false body least (zeroM M) (zeroM M) (zeroM M) _ target HEx)).
    exists d,e,j,body'. split;[exact HL1|]. split;assumption. }
  apply (proj1 (numerical_renaming_substitution M least (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1) least')) in HShift.
  rewrite Arithmetic.add_zero in HShift.
  pose proof (numerical_substitution_functional M least (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1)
    target least' STarget HShift) as E. subst least'.
  exists q. split;assumption.
Qed.

Print Assumptions source_least_ordinal_shift.
