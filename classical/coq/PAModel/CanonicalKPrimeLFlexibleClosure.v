(** Exact canonical K-prime closure from an arbitrary proof-wide L-domain
    table. Fresh auxiliary names may enlarge the table beyond n+2; they are
    handled by checked guarded closure and relative pure normalization. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalSetClosure NumericalContexts NumericalSourceFull ContextCombination SourceDomainContexts
  SourceZFRProvability SourceSetTheoryDescriptors SourceDescriptorProvability SourceRelativization
  SourceLFixed SourceLNonempty SourceNativeKRecipes NativeCanonicalLConsumer NativeEqualLBackground
  SourceGuardedDomainClosure SourceFlexibleDomainClosure.
Unset Implicit Arguments.
Local Opaque source_L_domain_code source_L_nonempty_code.

Definition canonical_upper_L_any_domain_proofs M :=forall phi n upper relative,
  source_bounded M phi (succM M(succM M n)) ->source_upper_conclusion_recipe M phi upper ->
  source_relativization M (source_L_domain_code M) upper relative ->
  exists k gb gc gn db dc ub uc ul,
    source_zfr_context M gb gc gn /\source_domain_context M (source_L_domain_code M) k db dc /\
    context_union M gb gc gn db dc k ub uc ul /\source_full_prv M ub uc ul relative.

Theorem canonical_kprime_L_images_from_any_domain M :
  canonical_upper_L_any_domain_proofs M ->canonical_kprime_L_images M.
Proof.
  intros HUpper phi n kprime closed HP(upper&all1&HU&HAll1&HAll2) HPrefix.
  destruct(source_relativization_total M (source_L_domain_code M) upper) as(relative&HR).
  destruct(HUpper phi n upper relative HP HU HR)
    as(k&gb&gc&gn&db&dc&ub&uc&ul&HG&HT&HUnion&P).
  destruct(source_relativization_total M (source_L_domain_code M) closed) as(rclosed&HRClosed).
  exists rclosed. split;[exact HRClosed|].
  apply(proj1(source_zfr_descriptor_provable M rclosed)).
  apply(source_descriptor_guarded_domain_close_any M ZFRSourceDescriptor
    (source_L_domain_code M)(source_L_nonempty_code M) gb gc gn k (succM M(succM M n))
    upper relative closed rclosed db dc ub uc ul).
  - exact(proj2(source_zfr_descriptor_context M gb gc gn) HG).
  - exact(numerical_L_domain_bounded M).
  - exact(native_L_nonempty_graph M).
  - exact(proj2(source_zfr_descriptor_provable M (source_L_nonempty_code M))(numerical_L_nonempty_zfr M)).
  - exact(source_upper_conclusion_recipe_bound M phi upper n HP HU).
  - apply(all_prefix_move_first M upper all1 HAll1 (succM M n)).
    exact(all_prefix_move_first M all1 kprime HAll2 n closed HPrefix).
  - exact HR.
  - exact HRClosed.
  - exact HT.
  - exact HUnion.
  - exact P.
Qed.

Print Assumptions canonical_kprime_L_images_from_any_domain.
