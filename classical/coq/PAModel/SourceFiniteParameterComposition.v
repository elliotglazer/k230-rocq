(** The finite parameter compiler respects the library's literal source
    substitution. This identifies fixed Ord0(t) occurrences inside larger
    finite laws with the unary Ord0 instance graph. *)
From PAModel Require Import CodeExpressions SetFormulaCodes SetSchemaConstructors
  SourceFiniteParameters SourceFiniteParameterBounds SubstitutionSource.
From FOL Require Import FullSyntax.
From Undecidability.FOL Require Import Syntax.Bounded Syntax.Core Syntax.BinSig Sets.Signatures.
Unset Implicit Arguments.

Lemma source_parameter_atom_substitution {ff} (P:ZF_Preds) (ts:Vector.t sf_term 2) names sigma :
  source_parameter_expression names
    (subst_form sigma (atom P ts:@Core.form sig_empty ZFSignature.ZF_pred_sig full_operators ff)) =
  E_sf (match P with elem=>SFMember | equal=>SFEqual end)
    (names (sf_index (sigma (sf_index (Vector.hd ts)))))
    (names (sf_index (sigma (sf_index (Vector.hd (Vector.tl ts)))))).
Proof.
  rewrite (Vector.eta ts),(Vector.eta (Vector.tl ts)).
  destruct P;cbn [subst_form source_parameter_expression Vector.map Vector.hd Vector.tl
    VectorDef.hd VectorDef.tl VectorDef.caseS];
    try rewrite !substitution_source_term_index;reflexivity.
Qed.

Theorem source_parameter_substitution {ff}
    (phi:@Core.form sig_empty ZFSignature.ZF_pred_sig full_operators ff) :
  forall names sigma,
  source_parameter_expression names (subst_form sigma phi) =
  source_parameter_expression (fun i=>names (sf_index (sigma i))) phi.
Proof.
  induction phi;intros names sigma.
  - reflexivity.
  - rewrite source_parameter_atom_substitution. destruct P;reflexivity.
  - cbn [subst_form source_parameter_expression]. rewrite IHphi1,IHphi2. reflexivity.
  - cbn [subst_form source_parameter_expression]. rewrite IHphi.
    f_equal. destruct (find_bounded phi) as [n HBound].
    apply (source_parameter_bounded_extensional n phi HBound).
    intros [|i] HI;rewrite source_up_substitution_index;cbn [source_parameter_up];reflexivity.
Qed.

Print Assumptions source_parameter_atom_substitution.
Print Assumptions source_parameter_substitution.
