(** Pure source proofs of both native vacuity conjuncts, followed by
    actual distinct-role canonical-core to full native-bundle assembly. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension CodeExpressions
  SetFormulaCodes SetCodeDescent SourceBounded SourceBoundMonotone NumericalContexts NumericalEnvironments
  NumericalContextRenaming NumericalRenamingMaps NumericalRenaming SourceQuantifierRules
  SourceSequents SourceTraceBounds NumericalSourceFull SourceImplicationAllShift SourceProofWeakening
  RawBinderRenaming RawSourceImage RawSourcePrivateBound NativeKBundle NativeVacuity
  SourceRoleAbstraction SourceNativeKRecipes NativeUpperNamedAlignment.
Unset Implicit Arguments.

Theorem source_vacuous_universal_empty M f shifted all out k :
  source_bounded M f k ->source_formula_shift M f shifted ->
  sf_relation M SFAll shifted (zeroM M) all ->sf_relation M SFImpl f all out ->
  source_full_prv M (zeroM M)(zeroM M)(zeroM M) out.
Proof.
  intros HF HS HA HO.
  pose proof (source_shift_bound M f shifted k HF HS) as HSB.
  pose proof (proj2 (source_bounded_accept_unary M SFAll shifted all k (or_introl eq_refl) HA) HSB) as HAllB.
  destruct (environment_cons_total M (zeroM M) (zeroM M) (zeroM M) f) as (b&c&n&HCons).
  assert (HC:context_bounded M b c n k).
  { apply (proj2 (context_bounded_cons M _ _ _ f b c n k HCons)). split;[exact HF|apply context_bounded_empty]. }
  destruct (context_shift_total M b c n) as (d&e&HShift).
  pose proof (context_shift_preserves_bound M b c n d e k HShift HC) as HDC.
  assert (HMember:context_member M b c n f).
  { apply (proj2 (context_member_cons M _ _ _ f b c n f HCons)). now left. }
  destruct (context_renaming_member_forward M b c n (zeroM M) (zeroM M) (zeroM M)
    (succM M (zeroM M)) d e f HShift HMember) as (sf&HSM&HR).
  rewrite (numerical_renaming_functional M f _ _ _ _ sf shifted HR HS) in HSM.
  apply (full_source_II M (zeroM M) (zeroM M) (zeroM M) f all out b c n).
  - exists k. split;[|apply context_bounded_empty].
    apply (proj2 (source_bounded_accept_binary M SFImpl f all out k ltac:(unfold sf_binary;auto) HO)). auto.
  - apply (full_source_AllI M b c n shifted all d e).
    + exists k. auto.
    + apply full_source_Ctx;[exists (succM M k);auto|exact HSM].
    + exact HShift.
    + exact HA.
  - exact HCons.
  - exact HO.
Qed.

Theorem native_atom_vacuity_empty M eq a b c u out :
  c<>a ->c<>b ->native_named_evaluation M (code_parameters a b c u)
    (NNTImpl (NNTAtom eq (CEvar 0) (CEvar 1))
      (NNTAll (CEvar 2) (NNTAtom eq (CEvar 0) (CEvar 1)))) out ->
  source_full_prv M (zeroM M)(zeroM M)(zeroM M) out.
Proof.
  intros HCA HCB (atom&all&(x&y&HX&HY&HAtom)&
    (name&body&rb&rc&closed&HN&(v&w&HV&HW&HBody)&HMap&HR&HAll)&HImp).
  change (x=a) in HX;change (y=b) in HY;change (name=c) in HN;
    change (v=a) in HV;change (w=b) in HW. subst x y name v w.
  rewrite (sf_relation_functional M (if eq then SFEqual else SFMember) a b body atom HBody HAtom) in HR.
  apply (source_vacuous_universal_empty M atom closed all out (succM M (addM M a b))).
  - apply (proj2 (source_bounded_accept_atom M (if eq then SFEqual else SFMember) a b atom _
      ltac:(destruct eq;unfold sb_atomic;auto) HAtom)).
    split;[apply coding_le_add|rewrite (add_comm M a b);apply coding_le_add].
  - exact (raw_binder_atom_avoids_is_shift M eq a b atom c rb rc closed HAtom HCA HCB HMap HR).
  - exact HAll.
  - exact HImp.
Qed.


Theorem native_vacuity_empty M a b c u out :
  c<>a ->c<>b ->native_named_evaluation M (code_parameters a b c u)
    (NNT_vacuity (CEvar 0)(CEvar 1)(CEvar 2)) out ->
  source_full_prv M (zeroM M)(zeroM M)(zeroM M) out.
Proof.
  intros HCA HCB HOut. destruct HOut as (left&right&HL&HR&HO).
  pose proof (native_atom_vacuity_empty M false a b c u left HCA HCB HL) as PL.
  pose proof (native_atom_vacuity_empty M true a b c u right HCA HCB HR) as PR.
  destruct (native_named_evaluation_bounded M (code_parameters a b c u)
    (NNT_vacuity (CEvar 0)(CEvar 1)(CEvar 2)) out
    (ex_intro _ left (ex_intro _ right (conj HL (conj HR HO))))) as (k&HK).
  apply (full_source_CI M (zeroM M)(zeroM M)(zeroM M) left right out);[exists k;split;[exact HK|apply context_bounded_empty]|exact PL|exact PR|exact HO].
Qed.

Theorem source_full_kprime_to_distinct_native_bundle M db dc dn a b c u phi abstract kprime native :
  a<>b ->c<>a ->c<>b ->raw_source_image M c phi ->
  source_role_abstraction M a b phi abstract ->source_kprime_core_recipe M abstract kprime ->
  native_named_evaluation M (code_parameters a b c u) native_K_bundle_template native ->
  source_full_prv M db dc dn kprime ->source_full_prv M db dc dn native.
Proof.
  intros Hab Hca Hcb HDecode HAbstract HKprime HNative HP.
  destruct HNative as (core&vacuity&HCore&HVacuity&HBundle).
  pose proof (source_full_kprime_to_distinct_named_core M db dc dn a b c u phi abstract kprime core
    Hab Hca Hcb HDecode (raw_source_image_private_bound M c phi HDecode) HAbstract HKprime HCore HP) as PCore.
  pose proof (native_vacuity_empty M a b c u vacuity Hca Hcb HVacuity) as PVacuity.
  destruct (source_full_prv_wellformed M db dc dn core PCore) as (k&HCoreBound&HContext).
  assert (PV:source_full_prv M db dc dn vacuity).
  { apply (source_full_prv_weaken_bounded M (zeroM M)(zeroM M)(zeroM M) db dc dn vacuity k PVacuity);[|exact HContext].
    intros f HF. exfalso. exact (context_empty M (zeroM M)(zeroM M) f HF). }
  destruct (native_named_evaluation_bounded M (code_parameters a b c u) native_K_bundle_template native
    (ex_intro _ core (ex_intro _ vacuity (conj HCore (conj HVacuity HBundle))))) as (l&HBound).
  apply (full_source_CI M db dc dn core vacuity native);[|exact PCore|exact PV|exact HBundle].
  exists (addM M l k). split.
  - exact (source_bounded_monotone M native l (addM M l k) HBound (coding_le_add M l k)).
  - apply (context_bounded_monotone M db dc dn k (addM M l k) HContext).
    rewrite Arithmetic.add_comm. apply coding_le_add.
Qed.

Print Assumptions native_vacuity_empty.
Print Assumptions source_full_kprime_to_distinct_native_bundle.


