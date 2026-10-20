(** Standard-model decoding of accepted source codes. This external finite
    syntax theorem complements the arbitrary-model arithmetic checker; it
    does not identify nonstandard codes with external finite syntax trees. *)
From PAModel Require Import Model FiniteCoding CodeExpressions StandardModel
  SetFormulaCodes SetCodeDescent SourceBounded SourceBoundedCalibration.
From FOL Require Import FullSyntax Arithmetics.
From Undecidability.FOL Require Import Syntax.BinSig Sets.Signatures.
From Stdlib Require Import Arith.PeanoNat Arith.Wf_nat.
Import Vector.VectorNotations.
Unset Implicit Arguments.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZFSignature.ZF_pred_sig | 0.

Lemma sf_relation_nat_value h a b f : sf_relation natModel h a b f -> f=sf_make h a b.
Proof.
  intro H. exact (sf_relation_functional natModel h a b f (sf_make h a b)
    H (sb_source_constructor_nat h a b)).
Qed.

Theorem source_bounded_has_syntax f :
  forall k, source_bounded natModel f k -> exists phi : sf_form, sf_encode phi=f.
Proof.
  induction f as [f H] using lt_wf_ind. intros k Hbound.
  destruct (sf_code_cases natModel f) as [Ef|[Hinvalid|[h [a [b Hf]]]]].
  - subst f. exists (falsity : sf_form). reflexivity.
  - exfalso. exact (source_bounded_reject_invalid natModel f k Hinvalid Hbound).
  - pose proof (sf_relation_descent natModel h a b f Hf) as [Ha Hb].
    apply sb_coding_lt_nat in Ha. apply sb_coding_lt_nat in Hb.
    pose proof (sf_relation_nat_value h a b f Hf) as Ef.
    destruct h.
    + exists (@Core.atom sig_empty ZFSignature.ZF_pred_sig full_operators falsity_on elem (Vector.cons _ (@Core.var sig_empty a) 1 (Vector.cons _ (@Core.var sig_empty b) 0 (Vector.nil _))) : sf_form). symmetry. exact Ef.
    + exists (@Core.atom sig_empty ZFSignature.ZF_pred_sig full_operators falsity_on equal (Vector.cons _ (@Core.var sig_empty a) 1 (Vector.cons _ (@Core.var sig_empty b) 0 (Vector.nil _))) : sf_form). symmetry. exact Ef.
    + apply (source_bounded_accept_binary natModel SFAnd a b f k (or_introl eq_refl) Hf) in Hbound.
      destruct (H a Ha k (proj1 Hbound)) as [pa Hpa].
      destruct (H b Hb k (proj2 Hbound)) as [pb Hpb].
      exists (@Core.bin sig_empty ZFSignature.ZF_pred_sig full_operators falsity_on Conj pa pb). cbn [sf_encode]. rewrite Hpa,Hpb. symmetry. exact Ef.
    + apply (source_bounded_accept_binary natModel SFOr a b f k (or_intror (or_introl eq_refl)) Hf) in Hbound.
      destruct (H a Ha k (proj1 Hbound)) as [pa Hpa].
      destruct (H b Hb k (proj2 Hbound)) as [pb Hpb].
      exists (@Core.bin sig_empty ZFSignature.ZF_pred_sig full_operators falsity_on Disj pa pb). cbn [sf_encode]. rewrite Hpa,Hpb. symmetry. exact Ef.
    + apply (source_bounded_accept_binary natModel SFImpl a b f k (or_intror (or_intror eq_refl)) Hf) in Hbound.
      destruct (H a Ha k (proj1 Hbound)) as [pa Hpa].
      destruct (H b Hb k (proj2 Hbound)) as [pb Hpb].
      exists (@Core.bin sig_empty ZFSignature.ZF_pred_sig full_operators falsity_on Impl pa pb). cbn [sf_encode]. rewrite Hpa,Hpb. symmetry. exact Ef.
    + change (sf_relation natModel SFAll a 0 f) in Hf.
      apply (source_bounded_accept_unary natModel SFAll a f k (or_introl eq_refl) Hf) in Hbound.
      destruct (H a Ha (S k) Hbound) as [pa Hpa].
      exists (@Core.quant sig_empty ZFSignature.ZF_pred_sig full_operators falsity_on All pa). cbn [sf_encode]. rewrite Hpa.
      exact (eq_sym (sf_relation_nat_value SFAll a 0 f Hf)).
    + change (sf_relation natModel SFEx a 0 f) in Hf.
      apply (source_bounded_accept_unary natModel SFEx a f k (or_intror eq_refl) Hf) in Hbound.
      destruct (H a Ha (S k) Hbound) as [pa Hpa].
      exists (@Core.quant sig_empty ZFSignature.ZF_pred_sig full_operators falsity_on Ex pa). cbn [sf_encode]. rewrite Hpa.
      exact (eq_sym (sf_relation_nat_value SFEx a 0 f Hf)).
Qed.

Theorem source_bounded_decode f k : source_bounded natModel f k <->
  exists phi : sf_form, bounded k phi /\ sf_encode phi=f.
Proof.
  split.
  - intro H. destruct (source_bounded_has_syntax f k H) as [phi Ephi].
    exists phi. split; [|exact Ephi].
    apply (proj1 (source_bounded_sf_encode phi k)). now rewrite Ephi.
  - intros [phi [Hbound Ephi]]. subst f.
    exact (proj2 (source_bounded_sf_encode phi k) Hbound).
Qed.

Print Assumptions source_bounded_has_syntax.
Print Assumptions source_bounded_decode.



