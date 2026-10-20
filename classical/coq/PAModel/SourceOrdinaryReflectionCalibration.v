(** Exact finite calibration of the actual ordinary hierarchy reflection graph. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceNumeralLift
 SourceOrdinaryReflectionSyntax SourceRelativizationCalibration SourceSetRelativizationCalibration
 SourceBallSCalibration SourceIffGraphs SourceHierarchySyntax SourceHierarchyCalibration
 SourceFiniteParameters SourceFiniteParameterIdentity OldNamedSyntaxBridge OldRelativizationBridge SourceLFixed.
From OldZFC Require Z_rel Z_refl Z_L.
From Undecidability.FOL Require Import Syntax.Core Syntax.BinSig Sets.Signatures Sets.minZF.
From FOL Require Import FullSyntax.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZFSignature.ZF_pred_sig | 0.
Lemma source_refl_numeral_zero M:code_numeral M 0=zeroM M. Proof. reflexivity. Qed.
Local Opaque code_numeral source_LL_predicate.
Lemma isolated_relS_variable {ff}(phi:isolated_old_form ff):forall y,
 isolated_formula(OldZFC.Z_rel.relS(@OC.var OB.sig_empty y)phi)=
 sf_relativize_set y(isolated_formula phi).
Proof.
 induction phi as[|ff P v|ff op a IHa b IHb|ff q a IH];intro y.
 - reflexivity.
 - destruct P;reflexivity.
 - cbn[OldZFC.Z_rel.relS isolated_formula sf_relativize_set]. now rewrite IHa,IHb.
 - destruct q.
   + change ((∀($0 ∈' $(S y) →isolated_formula(OldZFC.Z_rel.relS(@OC.var OB.sig_empty(S y))a)))=
       (∀($0 ∈' $(S y) →sf_relativize_set(S y)(isolated_formula a)))). now rewrite IH.
   + change ((∃($0 ∈' $(S y) ∧isolated_formula(OldZFC.Z_rel.relS(@OC.var OB.sig_empty(S y))a)))=
       (∃($0 ∈' $(S y) ∧sf_relativize_set(S y)(isolated_formula a)))). now rewrite IH.

Qed.
Lemma isolated_Refl_shape n phi d:
 isolated_formula(OldZFC.Z_refl.Refl n phi(@OC.var OB.sig_empty d))=
 ∀(isolated_formula(OldZFC.Z_L.LL(@OC.var OB.sig_empty(S d))(@OC.var OB.sig_empty 0)) →
 isolated_formula(OldZFC.Z_refl.ballS n(@OC.var OB.sig_empty 0)
  (@OC.bin OB.sig_empty OS.ZFSignature.ZF_pred_sig OC.FullSyntax.full_operators OC.falsity_on OC.FullSyntax.Conj
   (@OC.bin OB.sig_empty OS.ZFSignature.ZF_pred_sig OC.FullSyntax.full_operators OC.falsity_on OC.FullSyntax.Impl
    (OldRegCon.Rel.rel OldZFC.Z_L.Lform phi)(OldZFC.Z_rel.relS(@OC.var OB.sig_empty n)phi))
   (@OC.bin OB.sig_empty OS.ZFSignature.ZF_pred_sig OC.FullSyntax.full_operators OC.falsity_on OC.FullSyntax.Impl
    (OldZFC.Z_rel.relS(@OC.var OB.sig_empty n)phi)(OldRegCon.Rel.rel OldZFC.Z_L.Lform phi))))).
Proof. reflexivity. Qed.
Lemma source_encode_all_impl(a b:sf_form):sf_encode(∀(a→b))=
 sf_make SFAll(sf_make SFImpl(sf_encode a)(sf_encode b))0.
Proof. reflexivity. Qed.
Theorem source_ordinary_reflection_finite_lift M n(phi:isolated_old_form OC.falsity_on)d:
 source_ordinary_reflection M(source_L_domain_code M)(code_numeral M n)
  (code_numeral M(sf_encode(isolated_formula phi)))(code_numeral M d)
  (code_numeral M(sf_encode(isolated_formula(OldZFC.Z_refl.Refl n phi(@OC.var OB.sig_empty d))))).
Proof.
 set(left:=isolated_formula(OldRegCon.Rel.rel OldZFC.Z_L.Lform phi)).
 set(right:=isolated_formula(OldZFC.Z_rel.relS(@OC.var OB.sig_empty n)phi)).
 set(equiv:=isolated_formula(@OC.bin OB.sig_empty OS.ZFSignature.ZF_pred_sig OC.FullSyntax.full_operators OC.falsity_on OC.FullSyntax.Conj
   (@OC.bin OB.sig_empty OS.ZFSignature.ZF_pred_sig OC.FullSyntax.full_operators OC.falsity_on OC.FullSyntax.Impl
    (OldRegCon.Rel.rel OldZFC.Z_L.Lform phi)(OldZFC.Z_rel.relS(@OC.var OB.sig_empty n)phi))
   (@OC.bin OB.sig_empty OS.ZFSignature.ZF_pred_sig OC.FullSyntax.full_operators OC.falsity_on OC.FullSyntax.Impl
    (OldZFC.Z_rel.relS(@OC.var OB.sig_empty n)phi)(OldRegCon.Rel.rel OldZFC.Z_L.Lform phi)))).
 set(block:=isolated_formula(OldZFC.Z_refl.ballS n(@OC.var OB.sig_empty 0)
   (@OC.bin OB.sig_empty OS.ZFSignature.ZF_pred_sig OC.FullSyntax.full_operators OC.falsity_on OC.FullSyntax.Conj
   (@OC.bin OB.sig_empty OS.ZFSignature.ZF_pred_sig OC.FullSyntax.full_operators OC.falsity_on OC.FullSyntax.Impl
    (OldRegCon.Rel.rel OldZFC.Z_L.Lform phi)(OldZFC.Z_rel.relS(@OC.var OB.sig_empty n)phi))
   (@OC.bin OB.sig_empty OS.ZFSignature.ZF_pred_sig OC.FullSyntax.full_operators OC.falsity_on OC.FullSyntax.Impl
    (OldZFC.Z_rel.relS(@OC.var OB.sig_empty n)phi)(OldRegCon.Rel.rel OldZFC.Z_L.Lform phi))))).
 set(level:=isolated_formula(OldZFC.Z_L.LL(@OC.var OB.sig_empty(S d))(@OC.var OB.sig_empty 0))).
 rewrite isolated_Refl_shape. fold level block.
 exists(code_numeral M(sf_encode left)),(code_numeral M(sf_encode right)),
  (code_numeral M(sf_encode equiv)),(code_numeral M(sf_encode block)),
  (code_numeral M(sf_encode level)),(code_numeral M(sf_make SFImpl(sf_encode level)(sf_encode block))).
 split.
 - unfold left. rewrite isolated_relativization. apply source_relativization_finite_lift.
 - split.
   + unfold right. rewrite isolated_relS_variable. apply source_set_relativization_finite_lift.
   + split.
     * eapply source_iff_build;apply sf_make_numeral.
     * split.
       -- unfold block,equiv. Local Transparent code_numeral. exact(source_ballS_old_finite_lift M n 0 _).
       -- split.
          ++ unfold level. Local Transparent code_numeral.
             exact(source_parameter_LL_instance M CEconst(fun _=>zeroM M)(S d)0
              (code_numeral M(S d))(zeroM M)
              (code_numeral M(sf_encode(isolated_formula(OldZFC.Z_L.LL(@OC.var OB.sig_empty(S d))(@OC.var OB.sig_empty 0)))))
              eq_refl eq_refl(source_parameter_identity_numeral M _)).
          ++ split;[apply sf_make_numeral|].
             Local Opaque code_numeral.
             rewrite source_encode_all_impl.
             rewrite<-(source_refl_numeral_zero M).
             exact(sf_make_numeral M SFAll(sf_make SFImpl(sf_encode level)(sf_encode block))0).
Qed.
Print Assumptions isolated_relS_variable.
Print Assumptions source_ordinary_reflection_finite_lift.
