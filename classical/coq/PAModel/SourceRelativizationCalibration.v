(** Finite-source calibration of the same structural relativization.
    The arbitrary-domain case is useful to verify the guard placement;
    one-free-variable domains are required only for bound preservation. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceNumeralLift StandardModel
  SourceRelativizationRules SourceRelativization SourceRelativizationFunctionality.
From Undecidability.FOL Require Import Syntax.Core Syntax.BinSig Sets.Signatures.
From FOL Require Import FullSyntax.
Unset Implicit Arguments.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZFSignature.ZF_pred_sig | 0.

Definition sr_form ff := @Core.form sig_empty ZFSignature.ZF_pred_sig full_operators ff.
Fixpoint sf_relativize {ff} (domain:sf_form) (phi:sr_form ff) : sf_form :=
  match phi with
  | falsity => @falsity sig_empty ZFSignature.ZF_pred_sig full_operators
  | atom P args => @atom sig_empty ZFSignature.ZF_pred_sig full_operators falsity_on P args
  | bin op a b => @bin sig_empty ZFSignature.ZF_pred_sig full_operators falsity_on op
      (sf_relativize domain a) (sf_relativize domain b)
  | quant All a => @quant sig_empty ZFSignature.ZF_pred_sig full_operators falsity_on All
      (@bin sig_empty ZFSignature.ZF_pred_sig full_operators falsity_on Impl domain (sf_relativize domain a))
  | quant Ex a => @quant sig_empty ZFSignature.ZF_pred_sig full_operators falsity_on Ex
      (@bin sig_empty ZFSignature.ZF_pred_sig full_operators falsity_on Conj domain (sf_relativize domain a))
  end.

Theorem source_relativization_finite_lift {ff} M domain (phi:sr_form ff) :
  source_relativization M (code_numeral M (sf_encode domain))
    (code_numeral M (sf_encode phi)) (code_numeral M (sf_encode (sf_relativize domain phi))).
Proof.
  induction phi as [|ff P args|ff op a IHa b IHb|ff qu a IH].
  - apply source_relativization_falsity.
  - destruct P;cbn [sf_relativize sf_encode].
    + eapply source_relativization_atom;[now left|apply sf_make_numeral].
    + eapply source_relativization_atom;[now right|apply sf_make_numeral].
  - destruct op;cbn [sf_relativize sf_encode];
      eapply source_relativization_binary;try (apply sf_make_numeral);try assumption.
    + now left.
    + right;now left.
    + right;now right.
  - destruct qu;cbn [sf_relativize sf_encode].
    + eapply source_relativization_quantifier with (universal:=true)
        (a:=code_numeral M (sf_encode a))
        (w:=code_numeral M (sf_encode (sf_relativize domain a)));
        [exact (sf_make_numeral M SFAll (sf_encode a) 0)|exact IH|].
      exists (code_numeral M (sf_make SFImpl (sf_encode domain) (sf_encode (sf_relativize domain a)))).
      split.
      * exact (sf_make_numeral M SFImpl (sf_encode domain) (sf_encode (sf_relativize domain a))).
      * exact (sf_make_numeral M SFAll (sf_make SFImpl (sf_encode domain) (sf_encode (sf_relativize domain a))) 0).
    + eapply source_relativization_quantifier with (universal:=false)
        (a:=code_numeral M (sf_encode a))
        (w:=code_numeral M (sf_encode (sf_relativize domain a)));
        [exact (sf_make_numeral M SFEx (sf_encode a) 0)|exact IH|].
      exists (code_numeral M (sf_make SFAnd (sf_encode domain) (sf_encode (sf_relativize domain a)))).
      split.
      * exact (sf_make_numeral M SFAnd (sf_encode domain) (sf_encode (sf_relativize domain a))).
      * exact (sf_make_numeral M SFEx (sf_make SFAnd (sf_encode domain) (sf_encode (sf_relativize domain a))) 0).
Qed.

Theorem source_relativization_standard_exact {ff} domain (phi:sr_form ff) v :
  source_relativization natModel (sf_encode domain) (sf_encode phi) v <->
  v=sf_encode (sf_relativize domain phi).
Proof.
  pose proof (source_relativization_finite_lift natModel domain phi) as H.
  rewrite !numeral_natModel in H. split.
  - intro HV. exact (source_relativization_functional natModel (sf_encode phi)
      (sf_encode domain) v (sf_encode (sf_relativize domain phi)) HV H).
  - intros ->. exact H.
Qed.

Print Assumptions source_relativization_finite_lift.
Print Assumptions source_relativization_standard_exact.
