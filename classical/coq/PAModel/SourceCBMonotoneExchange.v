(** Literal exchange of the parameter and container in the Dn ordinal
    monotonicity law. The same map fixes both ordinal names. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SourceBounded
  NumericalRenamingMaps NumericalRenaming NumericalSubstitutionMaps NumericalSubstitution RenamingSubstitution
  SourceFixedSwap SourceSwap SourceQfRecipe SourceCBMonotoneMaps SourceOrdinalMonotoneMaps
  SourceFiniteCutoffShift SourceCutoffShiftCommutation SourceRenamingSquare SchemaRenamingDescriptors.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Definition source_cb_exchange_tail M rb rc rn:=exists ab ac an,
  renaming_lift M(code_numeral M 3)(code_numeral M 1)(code_numeral M 2)(zeroM M)ab ac an /\
  renaming_lift M ab ac an(zeroM M)rb rc rn.

Theorem source_cb_exchange_tail_total M:exists rb rc rn,source_cb_exchange_tail M rb rc rn.
Proof.
  destruct(renaming_lift_total M(code_numeral M 3)(code_numeral M 1)(code_numeral M 2)(zeroM M)) as(ab&ac&an&H1).
  destruct(renaming_lift_total M ab ac an(zeroM M)) as(rb&rc&rn&H2).
  exists rb,rc,rn,ab,ac,an. auto.
Qed.

Theorem source_cb_exchange_tail_small M rb rc rn i:
  source_cb_exchange_tail M rb rc rn ->(i<4)%nat ->
  renaming_lookup M rb rc rn(zeroM M)(code_numeral M i)
    (code_numeral M(match i with 0=>0|1=>1|2=>3|_=>2 end)).
Proof.
  intros(ab&ac&an&H1&H2)HI. destruct i as[|[|[|[|i]]]];try lia.
  - exact(proj1(proj2 H2)).
  - exact(proj2(proj2 H2)(zeroM M)(zeroM M)(proj1(proj2 H1))).
  - exact(proj2(proj2 H2)(code_numeral M 1)(code_numeral M 2)
      (proj2(proj2 H1)(zeroM M)(code_numeral M 1)(proj1(source_fixed_swap_map M)))).
  - exact(proj2(proj2 H2)(code_numeral M 2)(code_numeral M 1)
      (proj2(proj2 H1)(code_numeral M 1)(zeroM M)(proj2(source_fixed_swap_map M)))).
Qed.

Theorem source_cb_exchange_tail_outside M rb rc rn i:
  source_cb_exchange_tail M rb rc rn ->renaming_lookup M rb rc rn(zeroM M)
    (succM M(succM M(succM M(succM M i))))(succM M(succM M(succM M(succM M i)))).
Proof.
  intros(ab&ac&an&H1&H2). apply(proj2(proj2 H2)). apply(proj2(proj2 H1)). apply source_swap_tail.
Qed.

Theorem source_cb_dn_mono_matrix M(right:bool)dn q shifted rb rc rn out k:
  source_bounded M dn k ->
  numerical_renaming M dn(code_numeral M 210)(code_numeral M 6)(code_numeral M 3)(zeroM M)q ->
  source_cutoff_shift M(if right then 1 else 0)dn shifted ->
  source_cb_exchange_tail M rb rc rn ->numerical_renaming M shifted rb rc rn(zeroM M)out ->
  source_cb_mono_matrix M right q out.
Proof.
  intros HB HQ(sb&sc&sn&HMap&HShift)HT HR.
  apply(proj2(numerical_renaming_substitution M q _ _ _(code_numeral M 1)out)).
  rewrite descriptor_numeral_add.
  apply(numerical_source_renaming_square M dn k sb sc sn(code_numeral M(S(if right then 1 else 0)))
    (code_numeral M 210)(code_numeral M 6)(code_numeral M 3)(zeroM M)
    rb rc rn(zeroM M)(code_numeral M(source_oc_mono_dividend right))(code_numeral M 3)
    (code_numeral M 2)(code_numeral M 3)shifted q out HB HShift HQ HR).
  intros i j l m HI HFirst HSecond HThird.
  assert(HConvert:forall idx val,renaming_lookup M(code_numeral M(source_oc_mono_dividend right))
    (code_numeral M 3)(code_numeral M 2)(code_numeral M 1)idx val ->
    substitution_lookup M(code_numeral M(source_oc_mono_dividend right))(code_numeral M 3)
      (code_numeral M 2)(code_numeral M 3)idx val).
  { intros idx val HV. pose proof(proj1(renaming_substitution_lookup M _ _ _(code_numeral M 1)idx val)HV) as H.
    now rewrite descriptor_numeral_add in H. }
  destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)
    as[E|[idx E]];subst i.
  - pose proof(renaming_lookup_functional M _ _ _ _ _ l _ HThird(source_qf_exchange_zero M)) as E. subst l.
    destruct right;cbn[source_oc_mono_first source_oc_mono_dividend] in HMap,HFirst|-*.
    + pose proof(substitution_lookup_functional M _ _ _ _ _ j _ HFirst
        (source_cutoff_shift_map_fixed_lookup M 1 sb sc sn HMap 0)) as E. subst j.
      pose proof(renaming_lookup_functional M _ _ _ _ _ m _ HSecond
        (source_cb_exchange_tail_small M rb rc rn 0 HT ltac:(lia))) as E. subst m.
      exact(HConvert _ _(source_cb_mono_first M true)).
    + pose proof(substitution_lookup_functional M _ _ _ _ _ j _ HFirst
        (source_cutoff_shift_map_tail_lookup M 0 sb sc sn(zeroM M)HMap)) as E. subst j.
      pose proof(renaming_lookup_functional M _ _ _ _ _ m _ HSecond
        (source_cb_exchange_tail_small M rb rc rn 1 HT ltac:(lia))) as E. subst m.
      exact(HConvert _ _(source_cb_mono_first M false)).
  - destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)idx)
      as[E|[idx' E]];subst idx.
    + pose proof(renaming_lookup_functional M _ _ _ _ _ l _ HThird(source_qf_exchange_one M)) as E. subst l.
      assert(HLookup:substitution_lookup M sb sc sn(code_numeral M(S(if right then 1 else 0)))
        (code_numeral M 1)(code_numeral M 2)).
      { destruct right;[exact(source_cutoff_shift_map_tail_lookup M 1 sb sc sn(zeroM M)HMap)|
          exact(source_cutoff_shift_map_tail_lookup M 0 sb sc sn(code_numeral M 1)HMap)]. }
      pose proof(substitution_lookup_functional M _ _ _ _ _ j _ HFirst HLookup) as E. subst j.
      pose proof(renaming_lookup_functional M _ _ _ _ _ m _ HSecond
        (source_cb_exchange_tail_small M rb rc rn 2 HT ltac:(lia))) as E. subst m.
      exact(HConvert _ _(source_cb_mono_tail M right(zeroM M))).
    + destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)idx')
        as[E|[tail E]];subst idx'.
      * pose proof(renaming_lookup_functional M _ _ _ _ _ l _ HThird(source_qf_exchange_two M)) as E. subst l.
        assert(HLookup:substitution_lookup M sb sc sn(code_numeral M(S(if right then 1 else 0)))
          (code_numeral M 2)(code_numeral M 3)).
        { destruct right;[exact(source_cutoff_shift_map_tail_lookup M 1 sb sc sn(code_numeral M 1)HMap)|
            exact(source_cutoff_shift_map_tail_lookup M 0 sb sc sn(code_numeral M 2)HMap)]. }
        pose proof(substitution_lookup_functional M _ _ _ _ _ j _ HFirst HLookup) as E. subst j.
        pose proof(renaming_lookup_functional M _ _ _ _ _ m _ HSecond
          (source_cb_exchange_tail_small M rb rc rn 3 HT ltac:(lia))) as E. subst m.
        exact(HConvert _ _(source_cb_mono_second M right)).
      * assert(HNo:~coding_lt M(succM M(succM M(succM M tail)))(code_numeral M 3)).
        { intro H. exact(coding_not_lt_zero M tail(proj1(coding_lt_succ_cancel M tail(zeroM M))
            (proj1(coding_lt_succ_cancel M(succM M tail)(code_numeral M 1))
              (proj1(coding_lt_succ_cancel M(succM M(succM M tail))(code_numeral M 2))H)))). }
        pose proof(renaming_lookup_functional M _ _ _ _ _ l _ HThird(source_qf_exchange_outside M _ HNo)) as E. subst l.
        assert(HLookup:substitution_lookup M sb sc sn(code_numeral M(S(if right then 1 else 0)))
          (succM M(succM M(succM M tail)))(succM M(succM M(succM M(succM M tail))))).
        { destruct right;[exact(source_cutoff_shift_map_tail_lookup M 1 sb sc sn(succM M(succM M tail))HMap)|
            exact(source_cutoff_shift_map_tail_lookup M 0 sb sc sn(succM M(succM M(succM M tail)))HMap)]. }
        pose proof(substitution_lookup_functional M _ _ _ _ _ j _ HFirst HLookup) as E. subst j.
        pose proof(renaming_lookup_functional M _ _ _ _ _ m _ HSecond
          (source_cb_exchange_tail_outside M rb rc rn tail HT)) as E. subst m.
        exact(HConvert _ _(source_cb_mono_tail M right(succM M tail))).
Qed.

Print Assumptions source_cb_exchange_tail_total.
Print Assumptions source_cb_exchange_tail_small.
Print Assumptions source_cb_exchange_tail_outside.
Print Assumptions source_cb_dn_mono_matrix.
