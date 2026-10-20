(** Actual ZFR proof of the exact zero-parameter common-level recipe. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceNumeralLift
  OldNamedSyntaxBridge OldFullNDSourceBridge OldZFRProofLift SourceLNonempty SourceLFixed
  SourceCommonLevelBaseOld SourceCommonLevelRecipe SourceMembershipBlocks
  SourceParameterIdentityCalibration SourceOrdinalPredicate SourceOrdinalParameterCalibration SourceHierarchyCalibration
  SourceFiniteParameters SourceFiniteNameParameters SourceZFRProvability.
From OldZFC Require Z_base Z_L.
Unset Implicit Arguments.

Definition source_common_empty_ordinal :sf_form :=isolated_formula(OldZFC.Z_base.Ord0(@OC.var OB.sig_empty 1)).
Definition source_common_empty_level :sf_form :=isolated_formula(OldZFC.Z_L.LL(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 0)).
Definition source_common_empty :sf_form :=isolated_formula old_common_level_empty.
Lemma source_common_empty_shape : source_common_empty =
 @C.quant Undecidability.FOL.Syntax.BinSig.sig_empty S.ZFSignature.ZF_pred_sig C.FullSyntax.full_operators C.falsity_on C.FullSyntax.Ex
 (@C.quant Undecidability.FOL.Syntax.BinSig.sig_empty S.ZFSignature.ZF_pred_sig C.FullSyntax.full_operators C.falsity_on C.FullSyntax.Ex
  (@C.bin Undecidability.FOL.Syntax.BinSig.sig_empty S.ZFSignature.ZF_pred_sig C.FullSyntax.full_operators C.falsity_on C.FullSyntax.Conj
   (@C.bin Undecidability.FOL.Syntax.BinSig.sig_empty S.ZFSignature.ZF_pred_sig C.FullSyntax.full_operators C.falsity_on C.FullSyntax.Conj source_common_empty_ordinal source_common_empty_level)
   (@C.bin Undecidability.FOL.Syntax.BinSig.sig_empty S.ZFSignature.ZF_pred_sig C.FullSyntax.full_operators C.falsity_on C.FullSyntax.Impl
    (@C.falsity Undecidability.FOL.Syntax.BinSig.sig_empty S.ZFSignature.ZF_pred_sig C.FullSyntax.full_operators)
    (@C.falsity Undecidability.FOL.Syntax.BinSig.sig_empty S.ZFSignature.ZF_pred_sig C.FullSyntax.full_operators)))).
Proof. reflexivity. Qed.
Local Opaque source_ordinal_predicate_code source_common_empty_ordinal source_common_empty_level.

Lemma source_common_level_empty_graph M start :source_common_level_recipe M start (zeroM M)
  (code_numeral M(sf_encode source_common_empty)).
Proof.
  rewrite source_common_empty_shape. cbn [sf_encode].
  unfold source_common_level_recipe,source_common_level_data.
  set (o:=sf_encode source_common_empty_ordinal). set (y:=sf_encode source_common_empty_level).
  set (truth:=sf_make SFImpl 0 0). set (p:=sf_make SFAnd o y). set (body:=sf_make SFAnd p truth).
  exists (code_numeral M truth),(code_numeral M o),(code_numeral M y),(code_numeral M p),
    (code_numeral M body),(code_numeral M(sf_make SFEx body 0)).
  split.
  - apply source_membership_block_zero. exact (sf_make_numeral M SFImpl 0 0).
  - split.
    + exact (source_parameter_ordinal_instance M (fun j=>CEconst j)(fun _=>zeroM M) 1 (code_numeral M 1)
        (code_numeral M o) eq_refl (source_parameter_identity_calibration M source_common_empty_ordinal
          (fun j=>CEconst j)(fun _=>zeroM M)(fun _=>eq_refl))).
    + split.
      * exact (source_parameter_LL_instance M (fun j=>CEconst j)(fun _=>zeroM M) 1 0
          (code_numeral M 1)(zeroM M)(code_numeral M y) eq_refl eq_refl
          (source_parameter_identity_calibration M source_common_empty_level
            (fun j=>CEconst j)(fun _=>zeroM M)(fun _=>eq_refl))).
      * split;[exact (sf_make_numeral M SFAnd o y)|].
        split;[exact (sf_make_numeral M SFAnd p truth)|].
        split;[exact (sf_make_numeral M SFEx body 0)|].
        exact (sf_make_numeral M SFEx (sf_make SFEx body 0) 0).
Qed.

Theorem source_zfr_common_level_zero M start f :
  source_common_level_recipe M start (zeroM M) f ->source_zfr_provable M f.
Proof.
  intro HF. pose proof (source_common_level_recipe_functional M start (zeroM M) f
    (code_numeral M(sf_encode source_common_empty)) HF (source_common_level_empty_graph M start)) as E. subst f.
  exact (finite_old_zfr_proof_lift M old_L_background old_common_level_empty
    old_L_background_valid old_common_level_empty_proof).
Qed.
Print Assumptions source_common_level_empty_graph.
Print Assumptions source_zfr_common_level_zero.

