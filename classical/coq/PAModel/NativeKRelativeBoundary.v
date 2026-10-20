(** Relativize the whole pure closed implication, including its fixed
    background. This module never feeds a relative premise to an ordinary
    unrelativized source rule. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SetCodeDescent
  SourceBounded NumericalSetClosure SourceBoundedCalibration NumericalContexts NumericalSourceFull NumericalTheories
  SourceDescriptorProvability SourceDescriptorClosure SourceRelativeTheoryTransfer
  SourceRelativization SourceRelativizationBounds RawSourceImage RawSourcePrivateBound SourceRoleAbstraction
  SourceNativeKRecipes NativeKBundle NativeKUniformClosedImplication.
Unset Implicit Arguments.

Theorem source_descriptor_relative_pure_proof M T domain ex f relative :
  source_bounded M domain (code_numeral M 1) ->sf_relation M SFEx domain (zeroM M) ex ->
  source_descriptor_provable M T ex ->source_bounded M f (zeroM M) ->
  source_relativization M domain f relative ->
  source_full_prv M (zeroM M)(zeroM M)(zeroM M) f ->source_descriptor_provable M T relative.
Proof.
  intros HD HE (b&c&n&HC&PE) HF HR PF. exists b,c,n. split;[exact HC|].
  apply(source_relative_proof_transfer M domain ex b c n (zeroM M)(zeroM M)(zeroM M) f relative
    (proj1 HC) HD HE PE (source_relativization_preserves_bound M f domain (zeroM M) relative HD HF HR)
    HR);[|exact PF].
  intros a ra HA _. exfalso. exact(context_empty M (zeroM M)(zeroM M) a HA).
Qed.

Theorem native_kprime_uniform_relative_image M T domain ex a b private u phi abstract kprime closedK
    native n closedNative background relativeBG relativeK relativeNative :
  source_bounded M domain (code_numeral M 1) ->sf_relation M SFEx domain (zeroM M) ex ->
  source_descriptor_provable M T ex ->
  private<>a ->private<>b ->raw_source_image M private phi ->
  source_role_abstraction M a b phi abstract ->source_kprime_core_recipe M abstract kprime ->
  all_prefix M private kprime closedK ->
  native_named_evaluation M (code_parameters a b private u) native_K_bundle_template native ->
  source_bounded M native n ->all_prefix M n native closedNative ->native_equal_background M background ->
  source_relativization M domain background relativeBG ->source_descriptor_provable M T relativeBG ->
  source_relativization M domain closedK relativeK ->source_descriptor_provable M T relativeK ->
  source_relativization M domain closedNative relativeNative ->source_descriptor_provable M T relativeNative.
Proof.
  intros HD HE PE HPA HPB HDecode HAbstract HK HKPrefix HNative HNBound HNPrefix HBG
    HRBG PBG HRK PK HRN.
  destruct(sf_relation_total M SFImpl closedK closedNative) as(inner&HInner).
  destruct(sf_relation_total M SFImpl background inner) as(out&HOut).
  pose proof(native_kprime_uniform_closed_implication M a b private u phi abstract kprime closedK
    native n closedNative background inner out HPA HPB HDecode HAbstract HK HKPrefix HNative HNBound
    HNPrefix HBG HInner HOut) as PPure.
  pose proof(all_prefix_closes M n native closedNative HNBound HNPrefix) as HClosedN.
  pose proof(native_equal_background_closed M background HBG) as HClosedBG.
  destruct(source_full_prv_wellformed M (zeroM M)(zeroM M)(zeroM M) out PPure) as(k&HBound&_).
  assert(HClosedOut:source_bounded M out (zeroM M)).
  { pose proof(source_role_abstraction_bounded M a b phi abstract private
      (raw_source_image_private_bound M private phi HDecode) HAbstract) as HAB.
    pose proof(source_kprime_core_recipe_bound M abstract kprime private HAB HK) as HKB.
    pose proof(all_prefix_closes M private kprime closedK HKB HKPrefix) as HClosedK.
    apply(proj2(source_bounded_accept_binary M SFImpl background inner out (zeroM M)
      (or_intror(or_intror eq_refl)) HOut));split;[exact HClosedBG|].
    apply(proj2(source_bounded_accept_binary M SFImpl closedK closedNative inner (zeroM M)
      (or_intror(or_intror eq_refl)) HInner));auto. }
  destruct(sf_relation_total M SFImpl relativeK relativeNative) as(relativeInner&HRInner).
  destruct(sf_relation_total M SFImpl relativeBG relativeInner) as(relativeOut&HROut).
  assert(HRelOut:source_relativization M domain out relativeOut).
  { apply(source_relativization_binary M domain SFImpl background inner out relativeBG relativeInner relativeOut
      (or_intror(or_intror eq_refl)) HOut HRBG);[|exact HROut].
    exact(source_relativization_binary M domain SFImpl closedK closedNative inner relativeK relativeNative relativeInner
      (or_intror(or_intror eq_refl)) HInner HRK HRN HRInner). }
  pose proof(source_descriptor_relative_pure_proof M T domain ex out relativeOut HD HE PE HClosedOut HRelOut PPure) as PRelative.
  exact(source_descriptor_provable_mp M T relativeK relativeNative relativeInner PK
    (source_descriptor_provable_mp M T relativeBG relativeInner relativeOut PBG PRelative HROut) HRInner).
Qed.

Print Assumptions source_descriptor_relative_pure_proof.
Print Assumptions native_kprime_uniform_relative_image.
