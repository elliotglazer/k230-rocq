(** The quotient translation commutes with the explicit old/current source
    constructor map, uniformly in the source formula and domain term. *)
From PAModel Require Import OldNamedSyntaxBridge QuotationQTrans QuotientAtomTemplates.
From OldK230S Require KQuot KQuotFormula.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
Unset Implicit Arguments.

Lemma isolated_dmem_exact t x y :
  isolated_formula (OldK230S.KQuot.dmem t x y) =
  source_dmem (isolated_term t) (isolated_term x) (isolated_term y).
Proof. destruct t as [i|[]],x as [j|[]],y as [k|[]]. reflexivity. Qed.

Lemma isolated_deqv_exact t x y :
  isolated_formula (OldK230S.KQuot.deqv t x y) =
  source_deqv (isolated_term t) (isolated_term x) (isolated_term y).
Proof. destruct t as [i|[]],x as [j|[]],y as [k|[]]. reflexivity. Qed.

Lemma isolated_term_shift t :
  isolated_term (OC.subst_term (fun i => OC.var (S i)) t) =
  C.subst_term (fun i => C.var (S i)) (isolated_term t).
Proof. destruct t as [i|[]]. reflexivity. Qed.

Theorem isolated_quotient_translation_exact {ff} (phi : isolated_old_form ff) :
  forall t, isolated_formula (OldK230S.KQuotFormula.qtrans t phi) =
  source_qtrans (isolated_term t) (isolated_formula phi).
Proof.
  induction phi as [|ff p v|ff op a IHa b IHb|ff q a IH];intro t.
  - reflexivity.
  - destruct p; rewrite (OT.vec2 v);
      cbn [OldK230S.KQuotFormula.qtrans isolated_formula isolated_atom source_qtrans];
      rewrite ?isolated_dmem_exact,?isolated_deqv_exact; reflexivity.
  - cbn [OldK230S.KQuotFormula.qtrans isolated_formula source_qtrans].
    now rewrite IHa,IHb.
  - destruct q;destruct t as [i|[]];
      cbn [OldK230S.KQuotFormula.qtrans isolated_formula isolated_quant source_qtrans];
      rewrite IH;reflexivity.
Qed.

Print Assumptions isolated_dmem_exact.
Print Assumptions isolated_deqv_exact.
Print Assumptions isolated_term_shift.
Print Assumptions isolated_quotient_translation_exact.
