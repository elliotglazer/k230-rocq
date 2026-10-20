(** Exact arbitrary-code map identities needed when the input/output order
    of the ordinal collection relation is reopened as an existential. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  NumericalRenamingMaps NumericalRenaming NumericalSubstitutionMaps NumericalSubstitution
  RenamingSubstitution SourceBounded SourceSwap SourceFixedSwap SourceShiftSpecialization
  SourceSubstitutionIdentity SourceSubstitutionRenaming SourceFiniteCutoffShift
  SourceCutoffShiftCommutation SourceDomainInstances NumericalInstantiation.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Lemma source_fixed_swap_substitution_lookup M i j :
  renaming_lookup M (code_numeral M 3) (code_numeral M 1) (code_numeral M 2) (zeroM M) i j <->
  substitution_lookup M (code_numeral M 3) (code_numeral M 1) (code_numeral M 2) (code_numeral M 2) i j.
Proof. rewrite renaming_substitution_lookup,coding_add_zero_r. reflexivity. Qed.

Theorem source_fixed_swap_twice M phi first second k :
  source_bounded M phi k ->
  numerical_renaming M phi (code_numeral M 3) (code_numeral M 1) (code_numeral M 2) (zeroM M) first ->
  numerical_renaming M first (code_numeral M 3) (code_numeral M 1) (code_numeral M 2) (zeroM M) second ->
  second=phi.
Proof.
  intros HB HFirst HSecond.
  pose proof (proj1 (numerical_renaming_substitution M phi (code_numeral M 3) (code_numeral M 1)
    (code_numeral M 2) (zeroM M) first) HFirst) as HS. rewrite coding_add_zero_r in HS.
  assert (HIdentity:numerical_substitution M phi (zeroM M) (zeroM M) (zeroM M) (zeroM M) second).
  { apply (numerical_substitution_then_renaming M phi k
      (code_numeral M 3) (code_numeral M 1) (code_numeral M 2) (code_numeral M 2)
      (code_numeral M 3) (code_numeral M 1) (code_numeral M 2) (zeroM M)
      (zeroM M) (zeroM M) (zeroM M) (zeroM M) first second HB HS HSecond).
    intros i j v HI HSI HJV.
    apply (proj2 (source_fixed_swap_substitution_lookup M i j)) in HSI.
    destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) i) as [E|[idx E]];subst i.
    - pose proof (renaming_lookup_functional M _ _ _ _ _ j _ HSI (proj1 (source_fixed_swap_map M))) as EJ.
      subst j.
      pose proof (renaming_lookup_functional M _ _ _ _ _ v _ HJV (proj2 (source_fixed_swap_map M))) as EV.
      subst v. apply source_empty_substitution_lookup.
    - destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
        (fun ax H rho=>axioms M ax rho H) idx) as [E|[idx' E]];subst idx.
      + pose proof (renaming_lookup_functional M _ _ _ _ _ j _ HSI (proj2 (source_fixed_swap_map M))) as EJ.
        subst j.
        pose proof (renaming_lookup_functional M _ _ _ _ _ v _ HJV (proj1 (source_fixed_swap_map M))) as EV.
        subst v. apply source_empty_substitution_lookup.
      + pose proof (renaming_lookup_functional M _ _ _ _ _ j _ HSI
          (source_swap_tail M (code_numeral M 3) (code_numeral M 1) idx')) as EJ. subst j.
        pose proof (renaming_lookup_functional M _ _ _ _ _ v _ HJV
          (source_swap_tail M (code_numeral M 3) (code_numeral M 1) idx')) as EV. subst v.
        apply source_empty_substitution_lookup. }
  apply (numerical_substitution_functional M phi (zeroM M) (zeroM M) (zeroM M) (zeroM M) second phi HIdentity).
  apply (numerical_substitution_identity_on_bound M phi _ _ _ _ k HB).
  intros i HI. apply source_empty_substitution_lookup.
Qed.

Theorem source_cutoff_two_lifted_swap M phi shifted out inserted k rb rc rn :
  source_bounded M phi k ->source_cutoff_shift M 2 phi shifted ->
  renaming_lift M (code_numeral M 3) (code_numeral M 1) (code_numeral M 2) (zeroM M) rb rc rn ->
  numerical_renaming M shifted rb rc rn (zeroM M) out ->source_cutoff_shift M 1 phi inserted ->out=inserted.
Proof.
  intros HB (sb&sc&sn&HSM&HS) HL HR (ib&ic&inlen&HIM&HI).
  assert (HOut:numerical_substitution M phi ib ic inlen (code_numeral M 2) out).
  { apply (numerical_substitution_then_renaming M phi k sb sc sn (code_numeral M 3)
      rb rc rn (zeroM M) ib ic inlen (code_numeral M 2) shifted out HB HS HR).
    intros i j v HBound HSI HJV.
    destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) i) as [E|[idx E]];subst i.
    - pose proof (substitution_lookup_functional M _ _ _ _ _ j _ HSI
        (source_cutoff_shift_map_fixed_lookup M 2 sb sc sn HSM 0)) as EJ. subst j.
      pose proof (renaming_lookup_functional M _ _ _ _ _ v _ HJV (proj1 (proj2 HL))) as EV. subst v.
      exact (source_cutoff_shift_map_fixed_lookup M 1 ib ic inlen HIM 0).
    - destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
        (fun ax H rho=>axioms M ax rho H) idx) as [E|[idx' E]];subst idx.
      + pose proof (substitution_lookup_functional M _ _ _ _ _ j _ HSI
          (source_cutoff_shift_map_fixed_lookup M 2 sb sc sn HSM 1)) as EJ. subst j.
        pose proof (proj2 (proj2 HL) (zeroM M) (code_numeral M 1)
          (proj1 (source_fixed_swap_map M))) as HV.
        pose proof (renaming_lookup_functional M _ _ _ _ _ v _ HJV HV) as EV. subst v.
        exact (source_cutoff_shift_map_tail_lookup M 1 ib ic inlen (zeroM M) HIM).
      + pose proof (substitution_lookup_functional M _ _ _ _ _ j _ HSI
          (source_cutoff_shift_map_tail_lookup M 2 sb sc sn idx' HSM)) as EJ. subst j.
        pose proof (proj2 (proj2 HL) (succM M (succM M idx')) (succM M (succM M idx'))
          (source_swap_tail M (code_numeral M 3) (code_numeral M 1) idx')) as HV.
        pose proof (renaming_lookup_functional M _ _ _ _ _ v _ HJV HV) as EV. subst v.
        exact (source_cutoff_shift_map_tail_lookup M 1 ib ic inlen (succM M idx') HIM). }
  exact (numerical_substitution_functional M phi ib ic inlen (code_numeral M 2) out inserted HOut HI).
Qed.

Theorem source_collection_domain_instance_renaming M domain i f rb rc rn delta g j :
  source_bounded M domain (code_numeral M 1) ->numerical_instantiation M domain i f ->
  numerical_renaming M f rb rc rn delta g ->renaming_lookup M rb rc rn delta i j ->
  numerical_instantiation M domain j g.
Proof.
  intros HD (b&c&HH&HF) HR HJ.
  destruct (substitution_singleton_total M j) as (d&e&HH'&HT).
  exists d,e. split;[exact HH'|].
  apply (numerical_substitution_then_renaming M domain (code_numeral M 1)
    b c (code_numeral M 1) (zeroM M) rb rc rn delta
    d e (code_numeral M 1) (zeroM M) f g HD HF HR).
  intros x y v HX HXY HYV. rewrite (domain_index_below_one M x HX) in HXY|-*.
  pose proof (substitution_lookup_functional M _ _ _ _ _ y i HXY HH) as EY. subst y.
  pose proof (renaming_lookup_functional M _ _ _ _ _ v j HYV HJ) as EV. now subst v.
Qed.

Print Assumptions source_fixed_swap_twice.
Print Assumptions source_cutoff_two_lifted_swap.
Print Assumptions source_collection_domain_instance_renaming.
