(** The distinct-role canonical upper conclusion specializes to the exact
    native named core, by actual coded substitutions and no semantic step. *)
From Stdlib Require Import List.
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs ProofTemplates
  SetFormulaCodes SetSchemaConstructors SchemaConstructorBounds NumericalSubstitutionMaps NumericalSubstitution
  SubstitutionPayloads NumericalRenaming SourceBounded SourceRoleAbstraction SourceRoleReopening
  SourceNativeKRecipes SourceNativeKMatrixMaps SourceEmittedClosureRecipe SourceNativeKShifts
  RawSourceImage NativeKBundle SourceNamedScopes SourceNamedScopeBinding SourceFiniteMapLifts
  NativeCoreLeafAlignment NativeCoreRootAlignment NativeEmittedDoubleAction NamedCoreScopedRecipe
  SourceSequents NumericalSourceFull SourceDoubleSpecialization.
Import ListNotations.
Unset Implicit Arguments.

Theorem native_upper_named_exact M a b c u phi abstract upper sb sc result native :
  a<>b ->c<>a ->c<>b ->raw_source_image M c phi ->source_bounded M phi c ->
  source_role_abstraction M a b phi abstract ->source_upper_conclusion_recipe M abstract upper ->
  source_role_reopening M a b sb sc ->
  numerical_substitution M upper sb sc (code_numeral M 2) (zeroM M) result ->
  native_named_evaluation M (code_parameters a b c u)
    (NNT_core (CEvar 0)(CEvar 1)(CEvar 2)(NNTHole 2)) native ->result=native.
Proof.
  intros Hab Hca Hcb HDecode HB (arb&arc&HM&HR)
    (p&h&shifted&atom&root&body&HP&HH&HS&HA&HRoot&HBody&HUpper) HOpen HSub HNative.
  destruct (proj1 (numerical_substitution_quantifier M false body upper sb sc
    (code_numeral M 2)(zeroM M) result HUpper) HSub)
    as (db&dc&dn&bodyOut&HL&HBSub&HResult).
  assert (HLifts:source_substitution_lifts M 1 sb sc (code_numeral M 2)(zeroM M) db dc dn).
  { exists sb,sc,(code_numeral M 2). split;[repeat split;reflexivity|exact HL]. }
  destruct (proj1 (numerical_substitution_binary M SFAnd root shifted body db dc dn
    (code_numeral M 1) bodyOut (or_introl eq_refl) HBody) HBSub)
    as (rootOut&closureOut&HRootSub&HClosureSub&HBodyOut).
  destruct (proj1 (numerical_substitution_binary M SFImpl p atom root db dc dn
    (code_numeral M 1) rootOut (or_intror(or_intror eq_refl)) HRoot) HRootSub)
    as (q0&atomOut&HQ0&HAtomSub&HRootOut).
  pose proof (native_core_root_alignment M a b c phi abstract p q0 arb arc sb sc db dc dn
    HB HM HR HP HOpen HLifts HQ0) as HScope0.
  destruct (proj1 (numerical_substitution_member M (code_numeral M 1)(zeroM M)
    atom db dc dn (code_numeral M 1) atomOut HA) HAtomSub)
    as (memberLeft&memberRight&HLeft&HRight&HAtomOut).
  assert (ELeft:memberLeft=succM M b).
  { pose proof (source_substitution_lifts_tail M 1 sb sc (code_numeral M 2)(zeroM M)
      db dc dn (zeroM M) b HLifts (proj1 HOpen)) as HT.
    exact (substitution_lookup_functional M _ _ _ _ _ memberLeft _ HLeft HT). }
  assert (ERight:memberRight=zeroM M).
  { exact (proj1 (substitution_lift_head M sb sc (code_numeral M 2)(zeroM M) db dc dn memberRight HL) HRight). }
  subst memberLeft memberRight.
  destruct HH as (matrixA&matrixB&matrixC&HKA&HKB&HKC&HFrame).
  destruct (source_emitted_double_action M matrixA matrixB matrixC h shifted closureOut sb sc db dc dn
    HFrame HS HLifts HClosureSub) as (qA&qB&qC&HActionA&HActionB&HActionC&HClosureOut).
  assert (Align:forall kind matrix out,source_native_k_matrix M kind abstract matrix ->
      emitted_leaf_actions M kind matrix out sb sc ->
      named_scope_renaming M (native_named_leaf_scope M kind a b c) phi out).
  { intros kind matrix out HK (cb&cc&cn&ob&oc&on&shift&HCut&HShift&HOpenL&HLast).
    exact (native_core_leaf_alignment M kind a b c phi abstract matrix shift out arb arc sb sc cb cc cn ob oc on
      Hab Hca Hcb HB HM HR HK HCut HShift HOpenL HLast). }
  pose proof (Align NativeKA matrixA qA HKA HActionA) as HScopeA.
  pose proof (Align NativeKB matrixB qB HKB HActionB) as HScopeB.
  pose proof (Align NativeKC matrixC qC HKC HActionC) as HScopeC.
  assert (HCode:code_relation M (named_core_scoped_env b q0 qA qB qC)
      (E_named_core_scoped (CEvar 0)(CEvar 1)(CEvar 2)(CEvar 3)(CEvar 4)) result).
  { set (env:=named_core_scoped_env b q0 qA qB qC).
    assert (HClosureCode:code_relation M env (E_source_emitted_closure (CEvar 2)(CEvar 3)(CEvar 4)) closureOut).
    { set (sigma:=fun i=>match i with 0=>CEvar 2|1=>CEvar 3|_=>CEvar 4 end).
      change (code_relation M env (code_subst sigma
        (E_source_emitted_closure (CEvar 0)(CEvar 1)(CEvar 2))) closureOut).
      apply (proj2 (code_subst_graph M env sigma (schema_env3 qA qB qC)
        ltac:(intros [|[|i]];reflexivity) _ closureOut)). exact HClosureOut. }
    assert (HAtomCode:code_relation M env (E_sf SFMember (CEadd (CEvar 0)(CEconst 1))(CEconst 0)) atomOut).
    { apply (proj2 (schema_expression_graph M env SFMember (CEadd (CEvar 0)(CEconst 1)) (CEconst 0) (succM M b)(zeroM M) atomOut
        ltac:(exists b,(code_numeral M 1);split;[reflexivity|];split;[reflexivity|symmetry;apply named_core_add_one]) eq_refl)).
      exact HAtomOut. }
    set (rootE:=E_sf SFImpl (CEvar 1)
      (E_sf SFMember (CEadd (CEvar 0)(CEconst 1))(CEconst 0))).
    set (closureE:=E_source_emitted_closure (CEvar 2)(CEvar 3)(CEvar 4)).
    assert (HRootCode:code_relation M env rootE rootOut).
    { exact (proj2 (schema_expression_graph M env SFImpl (CEvar 1)
        (E_sf SFMember (CEadd (CEvar 0)(CEconst 1))(CEconst 0)) q0 atomOut rootOut eq_refl HAtomCode) HRootOut). }
    assert (HBodyCode:code_relation M env (E_sf SFAnd rootE closureE) bodyOut).
    { exact (proj2 (schema_expression_graph M env SFAnd rootE closureE rootOut closureOut bodyOut
        HRootCode HClosureCode) HBodyOut). }
    change (code_relation M env (E_sf SFEx (E_sf SFAnd rootE closureE)(CEconst 0)) result).
    exact (proj2 (schema_expression_graph M env SFEx (E_sf SFAnd rootE closureE) (CEconst 0)
      bodyOut (zeroM M) result HBodyCode eq_refl) HResult). }
  symmetry. exact (native_named_core_scoped_exact M a b c u phi q0 qA qB qC native result
    Hab Hca Hcb HDecode HScope0 HScopeA HScopeB HScopeC HNative HCode).
Qed.

Theorem source_full_kprime_to_distinct_named_core M db dc dn a b c u phi abstract kprime native :
  a<>b ->c<>a ->c<>b ->raw_source_image M c phi ->source_bounded M phi c ->
  source_role_abstraction M a b phi abstract ->source_kprime_core_recipe M abstract kprime ->
  native_named_evaluation M (code_parameters a b c u)
    (NNT_core (CEvar 0)(CEvar 1)(CEvar 2)(NNTHole 2)) native ->
  source_full_prv M db dc dn kprime ->source_full_prv M db dc dn native.
Proof.
  intros Hab Hca Hcb HDecode HB HAbstract (upper&all1&HUpper&HAll1&HAll2) HNative HP.
  destruct (source_role_reopening_total M a b) as (sb&sc&HOpen).
  destruct (numerical_substitution_total M upper sb sc (code_numeral M 2)(zeroM M)) as (result&HSub).
  pose proof (native_upper_named_exact M a b c u phi abstract upper sb sc result native
    Hab Hca Hcb HDecode HB HAbstract HUpper HOpen HSub HNative) as E. subst result.
  apply (source_full_double_specialize M db dc dn upper all1 kprime a b sb sc native
    (succM M (succM M c))).
  - exact (source_upper_conclusion_recipe_bound M abstract upper c
      (source_role_abstraction_bounded M a b phi abstract c HB HAbstract) HUpper).
  - exact HAll1.
  - exact HAll2.
  - exact HOpen.
  - exact HSub.
  - exact HP.
Qed.

Print Assumptions native_upper_named_exact.
Print Assumptions source_full_kprime_to_distinct_named_core.
