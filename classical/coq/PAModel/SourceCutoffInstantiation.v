(** Instantiation moves through insertion above the bound witness, while
    its replacement variable and result both shift. All codes are internal. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SourceBounded SourceFiniteCutoffShift
  NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation NumericalRenamingMaps
  NumericalRenaming NumericalContextRenaming SubstitutionSource SourceQuantifierRules
  SourceRenamingSquare SourceShiftSpecialization SourceSeparationSpecializationMaps SourceCutoffShiftCommutation.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Theorem source_instantiation_cutoff_shift M f f' t out out' k :
  source_bounded M f k -> numerical_instantiation M f t out ->
  source_cutoff_shift M 1 f f' -> source_formula_shift M out out' ->
  numerical_instantiation M f' (succM M t) out'.
Proof.
  intros HB (ab&ac&HA&HS) (rb&rc&rn&HRM&HR) HT.
  destruct (substitution_singleton_total M (succM M t)) as (ub&uc&HU&_).
  exists ub,uc. split;[exact HU|].
  apply (numerical_source_renaming_square M f k ab ac (succM M (zeroM M)) (zeroM M)
    rb rc rn (code_numeral M 1) (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1)
    ub uc (succM M (zeroM M)) (zeroM M) out f' out' HB HS
    (source_cutoff_shift_map_renaming M 1 f f' rb rc rn HRM HR) HT).
  intros i j l m HI HSI HTJ HRI.
  apply (proj1 (source_cutoff_shift_map_renaming_lookup M 1 rb rc rn i l HRM)) in HRI.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i) as [E|[idx E]];subst i.
  - assert (EJ:j=t) by (exact (substitution_lookup_functional M ab ac _ _ _ j t HSI HA)). subst j.
    assert (EL:l=zeroM M).
    { exact (substitution_lookup_functional M rb rc rn (code_numeral M 2) (zeroM M) l _ HRI
        (source_cutoff_shift_map_fixed_lookup M 1 rb rc rn HRM 0)). }
    subst l. apply context_shift_lookup in HTJ. subst m. exact HU.
  - assert (EJ:j=idx).
    { exact (substitution_lookup_functional M ab ac _ _ _ j idx HSI
        (substitution_singleton_tail M ab ac idx)). }
    subst j. apply context_shift_lookup in HTJ. subst m.
    assert (EL:l=succM M (succM M idx)).
    { exact (substitution_lookup_functional M rb rc rn (code_numeral M 2) _ l _ HRI
        (source_cutoff_shift_map_tail_lookup M 1 rb rc rn idx HRM)). }
    subst l. apply substitution_singleton_tail.
Qed.

Theorem source_cutoff_thrice_specialization_two M phi p1 p2 p3 f1 f2 count :
  source_bounded M phi (succM M count) ->
  source_cutoff_shift M 1 phi p1 -> source_cutoff_shift M 1 p1 p2 ->
  source_cutoff_shift M 1 p2 p3 -> source_formula_shift M phi f1 ->
  source_formula_shift M f1 f2 -> numerical_instantiation M p3 (code_numeral M 2) f2.
Proof.
  intros HB H1 H2 H3 HS1 HS2.
  destruct (source_cutoff_one_renaming M phi p1 H1) as (rb&rc&rn&HL&HR).
  pose proof (source_lifted_shift_specialization M phi (succM M count) rb rc rn p1 HB HL HR) as HI.
  pose proof (source_cutoff_shift_bounded M 1 phi p1 count HB H1) as HB1.
  pose proof (source_cutoff_shift_bounded M 1 p1 p2 (succM M count) HB1 H2) as HB2.
  pose proof (source_instantiation_cutoff_shift M p1 p2 (zeroM M) phi f1
    (succM M (succM M count)) HB1 HI H2 HS1) as HI1.
  exact (source_instantiation_cutoff_shift M p2 p3 (code_numeral M 1) f1 f2
    (succM M (succM M (succM M count))) HB2 HI1 H3 HS2).
Qed.

Print Assumptions source_instantiation_cutoff_shift.
Print Assumptions source_cutoff_thrice_specialization_two.
