(** The native bundle's two atomic vacuity conjuncts are actual pure
    source theorems, uniformly in the model-valued distinct private name. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension CodeExpressions
  SetFormulaCodes SetCodeDescent SourceBounded NumericalContexts NumericalEnvironments
  NumericalContextRenaming NumericalRenamingMaps NumericalRenaming SourceQuantifierRules
  SourceSequents NumericalSourceFull SourceImplicationAllShift SourceZFCProvability SourceZFCBasicClosure
  RawBinderRenaming NativeKBundle.
Unset Implicit Arguments.

Theorem source_vacuous_universal M f shifted all out k :
  source_bounded M f k ->source_formula_shift M f shifted ->
  sf_relation M SFAll shifted (zeroM M) all ->sf_relation M SFImpl f all out ->
  source_zfc_provable M out.
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
  apply source_zfc_provable_from_empty.
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

Theorem raw_binder_atom_avoids_is_shift M (eq:bool) a b f private rb rc closed :
  sf_relation M (if eq then SFEqual else SFMember) a b f ->
  private<>a ->private<>b ->raw_binder_renaming M private rb rc ->
  numerical_renaming M f rb rc (succM M private) (succM M (zeroM M)) closed ->
  source_formula_shift M f closed.
Proof.
  intros HF HA HB HM HR.
  apply (proj1 (numerical_renaming_atom M eq a b f rb rc (succM M private)
    (succM M (zeroM M)) closed HF)) in HR.
  destruct HR as (x&y&HX&HY&HOut).
  apply (proj1 (HM a x)) in HX. apply (proj1 (HM b y)) in HY.
  destruct HX as [[E _]|[_ ->]];[congruence|].
  destruct HY as [[E _]|[_ ->]];[congruence|].
  apply (proj2 (numerical_renaming_atom M eq a b f (zeroM M) (zeroM M) (zeroM M)
    (succM M (zeroM M)) closed HF)). exists (succM M a),(succM M b). split.
  - apply (proj2 (context_shift_lookup M a (succM M a))). reflexivity.
  - split;[apply (proj2 (context_shift_lookup M b (succM M b)));reflexivity|exact HOut].
Qed.

Theorem native_atom_vacuity_source M eq a b c u out :
  c<>a ->c<>b ->native_named_evaluation M (code_parameters a b c u)
    (NNTImpl (NNTAtom eq (CEvar 0) (CEvar 1))
      (NNTAll (CEvar 2) (NNTAtom eq (CEvar 0) (CEvar 1)))) out ->
  source_zfc_provable M out.
Proof.
  intros HCA HCB (atom&all&(x&y&HX&HY&HAtom)&
    (name&body&rb&rc&closed&HN&(v&w&HV&HW&HBody)&HMap&HR&HAll)&HImp).
  change (x=a) in HX;change (y=b) in HY;change (name=c) in HN;
    change (v=a) in HV;change (w=b) in HW. subst x y name v w.
  rewrite (sf_relation_functional M (if eq then SFEqual else SFMember) a b body atom HBody HAtom) in HR.
  apply (source_vacuous_universal M atom closed all out (succM M (addM M a b))).
  - apply (proj2 (source_bounded_accept_atom M (if eq then SFEqual else SFMember) a b atom _
      ltac:(destruct eq;unfold sb_atomic;auto) HAtom)).
    split;[apply coding_le_add|rewrite (add_comm M a b);apply coding_le_add].
  - exact (raw_binder_atom_avoids_is_shift M eq a b atom c rb rc closed HAtom HCA HCB HMap HR).
  - exact HAll.
  - exact HImp.
Qed.

Print Assumptions source_vacuous_universal.
Print Assumptions native_atom_vacuity_source.
