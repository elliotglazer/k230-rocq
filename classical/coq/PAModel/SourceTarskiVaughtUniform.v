(** Actual uniform numerical Tarski-Vaught theorem. The induction is over
    arbitrary internal source codes, using a PA-definable proof predicate. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions NumericalProofs SetFormulaCodes SetCodeDescent
  SourceBounded SourceBoundMonotone NumericalContexts NumericalSourceFull
  SourceRelativization SourceRelativizationFunctionality SourceRelativizationBounds
  SourceSetRelativization SourceSetRelativizationFunctionality SourceSetRelativizationBounds
  SourceIffGraphs SourceQuantifierPieces SourceQuantifierPieceInversion SourcePCSPieces
  SourceTarskiVaughtInputs SourceTarskiVaughtInvariant SourceTarskiVaughtQuantifiers SourceBooleanIffPrograms.
Unset Implicit Arguments.

Theorem source_tv_binary M h a b phi:
  sf_binary h ->sf_relation M h a b phi ->source_tv_at M a ->source_tv_at M b ->source_tv_at M phi.
Proof.
  intros HH HShape IHa IHb domain count carrier left right equiv cb cc cn k HD HF BC HC HY HL HR HE HM HW HS.
  destruct(proj1(source_bounded_accept_binary M h a b phi count HH HShape)HF)as(HBA&HBB).
  destruct(source_relativization_binary_inv M domain h a b phi left HH HShape HL)as(la&lb&HLA&HLB&HLeft).
  destruct(source_set_relativization_binary_inv M carrier h a b phi right HH HShape HR)as(ra&rb&HRA&HRB&HRight).
  destruct(source_iff_total M la ra)as(ia&HIA).
  destruct(source_iff_total M lb rb)as(ib&HIB).
  assert(HWA:source_tv_witnesses M domain a count carrier cb cc cn).
  { intros pc body piece out HB HP HO. apply(HW pc body piece out);[|exact HP|exact HO].
    apply(proj2(source_quantifier_body_binary M h a b phi count pc body HH HShape)). now left. }
  assert(HWB:source_tv_witnesses M domain b count carrier cb cc cn).
  { intros pc body piece out HB HP HO. apply(HW pc body piece out);[|exact HP|exact HO].
    apply(proj2(source_quantifier_body_binary M h a b phi count pc body HH HShape)). now right. }
  pose proof(IHa domain count carrier la ra ia cb cc cn k HD HBA BC HC HY HLA HRA HIA HM HWA HS)as PIA.
  pose proof(IHb domain count carrier lb rb ib cb cc cn k HD HBB BC HC HY HLB HRB HIB HM HWB HS)as PIB.
  pose proof(source_bounded_monotone M a count k HBA HC)as BA.
  pose proof(source_bounded_monotone M b count k HBB HC)as BB.
  exact(source_full_iff_binary M cb cc cn h la lb ra rb left right ia ib equiv k HH BC
    (source_relativization_preserves_bound M a domain k la HD BA HLA)
    (source_relativization_preserves_bound M b domain k lb HD BB HLB)
    (source_set_relativization_preserves_bound M a carrier k ra HY BA HRA)
    (source_set_relativization_preserves_bound M b carrier k rb HY BB HRB)
    HLeft HRight HIA HIB HE PIA PIB).
Qed.

Theorem source_full_tarski_vaught M:forall phi,source_tv_at M phi.
Proof.
  apply(sf_code_induction M(source_tv_at M)).
  - apply source_tv_at_definable.
  - intros domain count carrier left right equiv cb cc cn k HD HF BC HC HY HL HR HE HM HW HS.
    rewrite(source_relativization_invalid_inv M domain(zeroM M)left(or_introl eq_refl)HL)in HE.
    rewrite(source_set_relativization_invalid_inv M carrier(zeroM M)right(or_introl eq_refl)HR)in HE.
    exact(source_full_iff_reflexive M cb cc cn(zeroM M)equiv k BC(source_bounded_accept_falsity M k)HE).
  - intros phi HInvalid domain count carrier left right equiv cb cc cn k HD HF BC HC HY HL HR HE HM HW HS.
    exfalso. exact(source_bounded_reject_invalid M phi count HInvalid HF).
  - intros i j phi HShape domain count carrier left right equiv cb cc cn k HD HF BC HC HY HL HR HE HM HW HS.
    rewrite(source_relativization_atom_inv M domain false i j phi left HShape HL)in HE.
    rewrite(source_set_relativization_atom_inv M carrier false i j phi right HShape HR)in HE.
    exact(source_full_iff_reflexive M cb cc cn phi equiv k BC(source_bounded_monotone M phi count k HF HC)HE).
  - intros i j phi HShape domain count carrier left right equiv cb cc cn k HD HF BC HC HY HL HR HE HM HW HS.
    rewrite(source_relativization_atom_inv M domain true i j phi left HShape HL)in HE.
    rewrite(source_set_relativization_atom_inv M carrier true i j phi right HShape HR)in HE.
    exact(source_full_iff_reflexive M cb cc cn phi equiv k BC(source_bounded_monotone M phi count k HF HC)HE).
  - exact(source_tv_binary M).
  - intros h body phi HH HShape IH. destruct HH as[HA|HE];subst h.
    + exact(source_tv_quantifier M true body phi HShape IH).
    + exact(source_tv_quantifier M false body phi HShape IH).
Qed.
Print Assumptions source_tv_binary.
Print Assumptions source_full_tarski_vaught.
