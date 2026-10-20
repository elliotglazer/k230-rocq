(** The exact OC constructor commutes with insertion above its two roles. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
  SourceBounded NumericalSubstitutionMaps NumericalSubstitution SourceSubstitutionIdentity
  SourceDomainInstances SourceOrdinalPredicate SourceFiniteCutoffShift SourceCutoffQuantifiers
  SourceCutoffTwoSwap SourceOrdinalCollectionRecipe SourceNumeralLift.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.

Theorem source_oc_form_cutoff_two M phi phi' oc oc' k :
  source_bounded M phi k ->source_oc_form M(source_ordinal_predicate_code M) phi oc ->
  source_cutoff_shift M 2 phi phi' ->source_cutoff_shift M 2 oc oc' ->
  source_oc_form M(source_ordinal_predicate_code M) phi' oc'.
Proof.
  intros HB (ord1&swapped&tail&inner&HOrd&HSwap&HTail&HInner&HOC) HPS
    (sb&sc&sn&HM&HS).
  apply(proj1(numerical_substitution_binary M SFAnd inner tail oc sb sc sn(code_numeral M 3) oc'
    (or_introl eq_refl) HOC)) in HS.
  destruct HS as (inner'&tail'&HSInner&HSTail&HOC').
  apply(proj1(numerical_substitution_binary M SFAnd ord1 swapped inner sb sc sn(code_numeral M 3) inner'
    (or_introl eq_refl) HInner)) in HSInner.
  destruct HSInner as (ord1'&swapped'&HSOrd&HSSwap&HInner').
  assert(HOrdBound:source_bounded M ord1(code_numeral M 2)).
  { exact(source_domain_instance_bound M(source_ordinal_predicate_code M)(code_numeral M 1) ord1
      (code_numeral M 2)(source_ordinal_predicate_bounded M)(coding_lt_succ M(code_numeral M 1)) HOrd). }
  assert(HOrdSelf:numerical_substitution M ord1 sb sc sn(code_numeral M 3) ord1).
  { apply(numerical_substitution_identity_on_bound M ord1 sb sc sn(code_numeral M 3)(code_numeral M 2) HOrdBound).
    intros i HI. destruct(source_numeral_initial_segment M 2 i HI) as (j&HJ&->).
    destruct j as [|[|j]];try lia.
    - exact(source_cutoff_shift_map_fixed_lookup M 2 sb sc sn HM 0).
    - exact(source_cutoff_shift_map_fixed_lookup M 2 sb sc sn HM 1). }
  pose proof(numerical_substitution_functional M ord1 sb sc sn(code_numeral M 3) ord1' ord1 HSOrd HOrdSelf) as E.
  subst ord1'.
  assert(HSwap':NumericalRenaming.numerical_renaming M phi'(code_numeral M 3)(code_numeral M 1)
    (code_numeral M 2)(zeroM M) swapped').
  { apply(source_cutoff_two_swap M phi phi' swapped swapped' k HB HPS HSwap).
    exists sb,sc,sn. split;assumption. }
  destruct HTail as (shifted&atom&neg&point&HShift&HAtom&HNeg&HPoint&HAll).
  assert(HCutTail:source_cutoff_shift M 2 tail tail') by (exists sb,sc,sn;auto).
  destruct(source_cutoff_quantifier_inv M 2 true point tail tail' HAll HCutTail)
    as (point'&HAll'&rb&rc&rn&HRM&HR).
  apply(proj1(numerical_substitution_binary M SFImpl atom neg point rb rc rn(code_numeral M 4) point'
    (or_intror(or_intror eq_refl)) HPoint)) in HR.
  destruct HR as (atom'&neg'&HSAtom&HSNeg&HPoint').
  apply(proj1(numerical_substitution_binary M SFImpl shifted(zeroM M) neg rb rc rn(code_numeral M 4) neg'
    (or_intror(or_intror eq_refl)) HNeg)) in HSNeg.
  destruct HSNeg as (shifted'&false'&HSShifted&HSFalse&HNeg').
  assert(HFalse:numerical_substitution M(zeroM M) rb rc rn(code_numeral M 4)(zeroM M)).
  { apply(proj2(numerical_substitution_invalid M(zeroM M) rb rc rn(code_numeral M 4)(zeroM M)
      (or_introl eq_refl))). reflexivity. }
  pose proof(numerical_substitution_functional M(zeroM M) rb rc rn(code_numeral M 4) false'(zeroM M) HSFalse HFalse) as E.
  subst false'.
  assert(HAtomSelf:numerical_substitution M atom rb rc rn(code_numeral M 4) atom).
  { apply(proj2(numerical_substitution_member M(zeroM M)(code_numeral M 2) atom rb rc rn(code_numeral M 4) atom HAtom)).
    exists(zeroM M),(code_numeral M 2). split.
    - exact(source_cutoff_shift_map_fixed_lookup M 3 rb rc rn HRM 0).
    - split;[exact(source_cutoff_shift_map_fixed_lookup M 3 rb rc rn HRM 2)|exact HAtom]. }
  pose proof(numerical_substitution_functional M atom rb rc rn(code_numeral M 4) atom' atom HSAtom HAtomSelf) as E.
  subst atom'.
  assert(HShift':source_cutoff_shift M 2 phi' shifted').
  { apply(source_cutoff_two_three_commute M phi shifted phi' shifted' k HB HShift HPS).
    exists rb,rc,rn. split;assumption. }
  exists ord1,swapped',tail',inner'. split;[exact HOrd|]. split;[exact HSwap'|].
  split;[|split;assumption]. exists shifted',atom,neg',point'. repeat split;assumption.
Qed.

Print Assumptions source_oc_form_cutoff_two.
