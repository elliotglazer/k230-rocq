(** Finite current and pinned-old relS calibration. The numerical graph
    itself acts on arbitrary internal matrices; this theorem identifies its
    literal moving-carrier convention with the original mathematical source. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceNumeralLift
  SourceRelativization SourceSetRelativizationRules SourceSetRelativization
  SourceSetRelativizationFunctionality.
From Undecidability.FOL Require Import Syntax.Core Syntax.BinSig Sets.Signatures Sets.minZF.
From FOL Require Import FullSyntax.
Unset Implicit Arguments.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZFSignature.ZF_pred_sig | 0.

Fixpoint sf_relativize_set {ff} (name:nat)
    (phi:@Core.form sig_empty ZFSignature.ZF_pred_sig full_operators ff) :sf_form :=
  match phi with
  | falsity=>@falsity sig_empty ZFSignature.ZF_pred_sig full_operators
  | atom P args=>@atom sig_empty ZFSignature.ZF_pred_sig full_operators falsity_on P args
  | bin op a b=>@bin sig_empty ZFSignature.ZF_pred_sig full_operators falsity_on op
      (sf_relativize_set name a)(sf_relativize_set name b)
  | quant All a=>∀($0 ∈' $(S name) →sf_relativize_set (S name) a)
  | quant Ex a=>∃($0 ∈' $(S name) ∧sf_relativize_set (S name) a)
  end.

Theorem source_set_relativization_finite_lift {ff} M
    (phi:@Core.form sig_empty ZFSignature.ZF_pred_sig full_operators ff) :forall name,
  source_set_relativization M (code_numeral M name)(code_numeral M(sf_encode phi))
    (code_numeral M(sf_encode(sf_relativize_set name phi))).
Proof.
  induction phi as[|ff P args|ff op a IHa b IHb|ff q a IH];intro name.
  - apply source_set_relativization_falsity.
  - destruct P;cbn[sf_relativize_set sf_encode];
      eapply source_set_relativization_atom;[now left|apply sf_make_numeral|now right|apply sf_make_numeral].
  - destruct op;cbn[sf_relativize_set sf_encode];
      eapply source_set_relativization_binary;try apply sf_make_numeral;try apply IHa;try apply IHb.
    + now left.
    + right;now left.
    + right;now right.
  - destruct q;cbn[sf_relativize_set sf_encode].
    + eapply source_set_relativization_quantifier with(universal:=true)
        (a:=code_numeral M(sf_encode a))
        (w:=code_numeral M(sf_encode(sf_relativize_set (S name) a))).
      * exact(sf_make_numeral M SFAll (sf_encode a) 0).
      * exact(IH(S name)).
      * exists(code_numeral M(sf_make SFMember 0 (S name))),
          (code_numeral M(sf_make SFImpl (sf_make SFMember 0 (S name))
            (sf_encode(sf_relativize_set (S name) a)))).
        split;[exact(sf_make_numeral M SFMember 0 (S name))|]. split.
        -- exact(sf_make_numeral M SFImpl (sf_make SFMember 0 (S name))
              (sf_encode(sf_relativize_set (S name) a))).
        -- exact(sf_make_numeral M SFAll (sf_make SFImpl (sf_make SFMember 0 (S name))
              (sf_encode(sf_relativize_set (S name) a))) 0).
    + eapply source_set_relativization_quantifier with(universal:=false)
        (a:=code_numeral M(sf_encode a))
        (w:=code_numeral M(sf_encode(sf_relativize_set (S name) a))).
      * exact(sf_make_numeral M SFEx (sf_encode a) 0).
      * exact(IH(S name)).
      * exists(code_numeral M(sf_make SFMember 0 (S name))),
          (code_numeral M(sf_make SFAnd (sf_make SFMember 0 (S name))
            (sf_encode(sf_relativize_set (S name) a)))).
        split;[exact(sf_make_numeral M SFMember 0 (S name))|]. split.
        -- exact(sf_make_numeral M SFAnd (sf_make SFMember 0 (S name))
              (sf_encode(sf_relativize_set (S name) a))).
        -- exact(sf_make_numeral M SFEx (sf_make SFAnd (sf_make SFMember 0 (S name))
              (sf_encode(sf_relativize_set (S name) a))) 0).
Qed.

Print Assumptions source_set_relativization_finite_lift.
