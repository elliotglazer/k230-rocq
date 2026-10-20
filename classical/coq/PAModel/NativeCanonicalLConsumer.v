(** The sole varying-matrix premise here is the literal closed canonical
    K-prime image in L. Role normalization, equal active names, fixed
    Empty/Hosting background, and actual relativized proof application
    have all been discharged. This is still a conditional K-in-L theorem. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalSetClosure SourceDescriptorProvability SourceSetTheoryDescriptors SourceZFRProvability
  SourceRelativization RawSourceImage RawSourcePrivateBound SourceRoleAbstraction SourceNativeKRecipes NativeKBundle
  NativeKBundleRelativeImages NativeKUniformClosedImplication NativeKRelativeBoundary
  NativeEqualBackgroundCalibration NativeEqualLBackground SourceLFixed SourceLNonempty.
Unset Implicit Arguments.
Local Opaque source_L_domain_code source_L_nonempty_code.

Definition canonical_kprime_L_images M :=forall phi n kprime closed,
  source_bounded M phi (succM M(succM M n)) ->source_kprime_core_recipe M phi kprime ->
  all_prefix M n kprime closed ->exists relative,
    source_relativization M (source_L_domain_code M) closed relative /\source_zfr_provable M relative.

Theorem native_K_L_images_from_canonical M :canonical_kprime_L_images M ->
  native_K_relative_images M ZFRSourceDescriptor (source_L_domain_code M).
Proof.
  intros HCanonical a b private u native bound closed HPA HPB HNative HBound HPrefix.
  destruct(raw_source_image_total M private) as(phi&HDecode).
  destruct(source_role_abstraction_total M a b phi) as(abstract&HAbstract).
  pose proof(source_role_abstraction_bounded M a b phi abstract private
    (raw_source_image_private_bound M private phi HDecode) HAbstract) as HAB.
  destruct(source_kprime_core_recipe_total M abstract) as(kprime&HK).
  destruct(all_prefix_total M private kprime) as(closedK&HKPrefix).
  destruct(HCanonical abstract private kprime closedK HAB HK HKPrefix) as(relativeK&HRK&PK).
  destruct(sf_relation_total M SFAnd (code_numeral M(sf_encode source_equal_empty))
    (code_numeral M(sf_encode source_equal_hosting))) as(background&HBG).
  destruct(source_relativization_total M (source_L_domain_code M) background) as(relativeBG&HRBG).
  pose proof(numerical_L_native_equal_background M background relativeBG HBG HRBG) as PBG.
  destruct(source_relativization_total M (source_L_domain_code M) closed) as(relative&HR).
  exists relative. split;[exact HR|].
  apply(native_kprime_uniform_relative_image M ZFRSourceDescriptor (source_L_domain_code M)
    (source_L_nonempty_code M) a b private u phi abstract kprime closedK native bound closed
    background relativeBG relativeK relative).
  - exact(numerical_L_domain_bounded M).
  - exact(native_L_nonempty_graph M).
  - exact(proj2(source_zfr_descriptor_provable M (source_L_nonempty_code M))(numerical_L_nonempty_zfr M)).
  - exact HPA.
  - exact HPB.
  - exact HDecode.
  - exact HAbstract.
  - exact HK.
  - exact HKPrefix.
  - exact HNative.
  - exact HBound.
  - exact HPrefix.
  - exact HBG.
  - exact HRBG.
  - exact(proj2(source_zfr_descriptor_provable M relativeBG) PBG).
  - exact HRK.
  - exact(proj2(source_zfr_descriptor_provable M relativeK) PK).
  - exact HR.
Qed.

Print Assumptions native_K_L_images_from_canonical.
