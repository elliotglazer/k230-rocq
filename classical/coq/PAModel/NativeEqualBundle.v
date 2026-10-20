(** The complete native K bundle for equal active names. Only actual
    Empty and one-object Hosting source proofs are required. The decoded
    matrix remains arbitrary, and the ambient proof context is unrestricted. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalContexts NumericalSourceFull RawSourceImage RawSourcePrivateBound
  NativeKBundle NativeBundleAssembly SourceNamedQuantifierRules NativeEmptyClosure
  NativeEqualCarrierBranches NativeEqualCoreCase SourceNamedProofRules.
Unset Implicit Arguments.

Theorem source_full_equal_native_bundle M b c n a private u phi member host empty emptyExists native :
  private<>a ->raw_source_image M private phi ->sf_relation M SFMember a private member ->
  source_named_quantifier M false private member host ->source_named_empty M a private empty ->
  source_named_quantifier M false private empty emptyExists ->
  native_named_evaluation M (code_parameters a a private u) native_K_bundle_template native ->
  source_full_prv M b c n host ->source_full_prv M b c n emptyExists ->source_full_prv M b c n native.
Proof.
  intros HPrivate HDecode HMember HHost HEmpty HEmptyExists HNative PHost PEmpty.
  destruct HNative as(core&vacuity&HCore&HVacuity&HBundle).
  assert (HPhi:native_named_evaluation M (code_parameters a a private u)(NNTHole 2) phi).
  { exact HDecode. }
  pose proof(native_equal_core_from_empty_host M b c n (code_parameters a a private u)
    (CEvar 0)(CEvar 2)(NNTHole 2) a private phi member host empty emptyExists core
    eq_refl eq_refl HPhi (raw_source_image_private_bound M private phi HDecode)
    HMember HHost HEmpty HEmptyExists HCore PHost PEmpty) as PCore.
  pose proof(native_vacuity_empty M a a private u vacuity HPrivate HPrivate HVacuity) as PV.
  destruct(source_full_prv_wellformed M b c n core PCore) as(k&_&HC).
  exact(source_full_and_intro M b c n core vacuity native HBundle PCore
    (source_full_weaken_empty M b c n vacuity k HC PV)).
Qed.

Print Assumptions source_full_equal_native_bundle.
