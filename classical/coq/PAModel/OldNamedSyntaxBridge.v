(** Constructor correspondence between the isolated original named compiler
    and the current finite-policy compiler. No provability premise is used. *)
From OldUndecidability.FOL.Syntax Require Core BinSig.
From OldUndecidability.FOL.Sets Require Signatures minZF.
From OldZF Require Logic Std_tr.
From OldK230S Require KQuotFormula.
From OldK230L Require Comp_Prop230.
From Undecidability.FOL Require Import Syntax.Core Syntax.BinSig Sets.Signatures Sets.minZF.
From PAModel Require Import CodeExpressions ProofTemplates SetFormulaCodes
  FiniteNamedPolicies QuotationQTrans QuotientAtomTemplates.
From Stdlib Require Import Vectors.Vector.

Module OC := OldUndecidability.FOL.Syntax.Core.
Module OB := OldUndecidability.FOL.Syntax.BinSig.
Module OS := OldUndecidability.FOL.Sets.Signatures.
Module OT := OldZF.Std_tr.
Module OL := OldZF.Logic.
Module OP := OldK230L.Comp_Prop230.
Module C := Undecidability.FOL.Syntax.Core.
Module S := Undecidability.FOL.Sets.Signatures.
Unset Implicit Arguments.

Definition isolated_old_term := @OC.term OB.sig_empty.
Definition isolated_old_form ff :=
  @OC.form OB.sig_empty OS.ZFSignature.ZF_pred_sig OC.FullSyntax.full_operators ff.
Definition isolated_current_form ff :=
  @C.form BinSig.sig_empty S.ZFSignature.ZF_pred_sig C.FullSyntax.full_operators ff.
Definition isolated_flag ff :=
  match ff with OC.falsity_on => C.falsity_on | OC.falsity_off => C.falsity_off end.
Definition isolated_term (t : isolated_old_term) : set_term :=
  match t with OC.var i => C.var i | OC.func f _ => False_rect _ f end.
Definition isolated_op op :=
  match op with OC.FullSyntax.Conj => C.FullSyntax.Conj
  | OC.FullSyntax.Disj => C.FullSyntax.Disj | OC.FullSyntax.Impl => C.FullSyntax.Impl end.
Definition isolated_quant q :=
  match q with OC.FullSyntax.All => C.FullSyntax.All | OC.FullSyntax.Ex => C.FullSyntax.Ex end.
Definition isolated_atom {ff} (p : OS.ZF_Preds)
    (v : Vector.t isolated_old_term (OS.ZF_pred_ar p)) :
    isolated_current_form (isolated_flag ff) :=
  match p return Vector.t isolated_old_term (OS.ZF_pred_ar p) ->
      isolated_current_form (isolated_flag ff) with
  | OS.elem => fun v => @C.atom BinSig.sig_empty S.ZFSignature.ZF_pred_sig
      C.FullSyntax.full_operators _ S.elem (Vector.map isolated_term v)
  | OS.equal => fun v => @C.atom BinSig.sig_empty S.ZFSignature.ZF_pred_sig
      C.FullSyntax.full_operators _ S.equal (Vector.map isolated_term v)
  end v.
Fixpoint isolated_formula {ff} (phi : isolated_old_form ff) :
    isolated_current_form (isolated_flag ff) :=
  match phi in @OC.form _ _ _ f return isolated_current_form (isolated_flag f) with
  | OC.falsity => @C.falsity BinSig.sig_empty S.ZFSignature.ZF_pred_sig C.FullSyntax.full_operators
  | OC.atom p v => isolated_atom p v
  | OC.bin op a b => @C.bin BinSig.sig_empty S.ZFSignature.ZF_pred_sig
      C.FullSyntax.full_operators _ (isolated_op op) (isolated_formula a) (isolated_formula b)
  | OC.quant q a => @C.quant BinSig.sig_empty S.ZFSignature.ZF_pred_sig
      C.FullSyntax.full_operators _ (isolated_quant q) (isolated_formula a)
  end.

Fixpoint isolated_named_expression (a : OL.wff) : code_expr :=
  match a with
  | OL.Weq x y => E_weq (CEconst x) (CEconst y)
  | OL.Wel x y => E_wel (CEconst x) (CEconst y)
  | OL.Wim a b => E_wim (isolated_named_expression a) (isolated_named_expression b)
  | OL.Wn a => E_wn (isolated_named_expression a)
  | OL.Wal x a => E_wal (CEconst x) (isolated_named_expression a)
  end.

Theorem isolated_named_expression_value rho a :
  code_value rho (isolated_named_expression a) = OP.tau a.
Proof.
  induction a; cbn [isolated_named_expression OP.tau];
    repeat first [rewrite code_value_weq | rewrite code_value_wel |
      rewrite code_value_wim | rewrite code_value_wn | rewrite code_value_wal].
  - reflexivity.
  - reflexivity.
  - now rewrite IHa1,IHa2.
  - now rewrite IHa.
  - now rewrite IHa.
Qed.

Lemma isolated_formula_depth {ff} (phi : isolated_old_form ff) :
  named_policy_depth (isolated_formula phi) = OT.qd phi.
Proof.
  induction phi as [|ff p v|ff op a IHa b IHb|ff q a IH].
  - reflexivity.
  - destruct p; reflexivity.
  - cbn [isolated_formula named_policy_depth OT.qd]. now rewrite IHa,IHb.
  - cbn [isolated_formula named_policy_depth OT.qd]. now rewrite IH.
Qed.

Theorem isolated_tr_named_policy {ff} (phi : isolated_old_form ff) :
  forall eta env fresh, (forall i, env i = CEconst (eta i)) ->
  isolated_named_expression (OT.tr eta phi) =
  named_policy_formula true (named_bottom_expression (CEconst 0))
    depth_binder_policy env fresh (isolated_formula phi).
Proof.
  induction phi as [|ff p v|ff op a IHa b IHb|ff q a IH]; intros eta env fresh HE.
  - reflexivity.
  - destruct p; rewrite (OT.vec2 v);
      destruct (Vector.hd v) as [i|[]];
      destruct (Vector.hd (Vector.tl v)) as [j|[]];
      cbn [OT.tr OT.tv isolated_formula isolated_atom isolated_term
        isolated_named_expression named_policy_formula template_term];
      cbn; now rewrite !HE.
  - destruct op.
    + cbn [OT.tr isolated_formula isolated_op named_policy_formula
        isolated_named_expression OL.Wa].
      now rewrite (IHa eta env fresh HE),(IHb eta env fresh HE).
    + cbn [OT.tr isolated_formula isolated_op named_policy_formula
        isolated_named_expression E_or].
      now rewrite (IHa eta env fresh HE),(IHb eta env fresh HE).
    + destruct b; try destruct P;
        cbn [OT.tr isolated_formula isolated_op isolated_atom named_policy_formula
          isolated_named_expression] in IHb |- *;
        rewrite (IHa eta env fresh HE); try reflexivity;
        rewrite (IHb eta env fresh HE); reflexivity.
  - destruct q; cbn [OT.tr isolated_formula isolated_quant named_policy_formula
        isolated_named_expression OL.Wex];
      rewrite isolated_formula_depth; unfold depth_binder_policy,OT.bname;
      rewrite (IH (OC.scons (2 * OT.qd a + 2) eta)
        (fun i => match i with 0 => CEconst (2 * OT.qd a + 2) | S j => env j end)
        (CEadd fresh (CEconst 1))
        ltac:(intros [|i];cbn;[reflexivity|apply HE])); reflexivity.
Qed.

Corollary isolated_tr_code_value {ff} (phi : isolated_old_form ff) eta fresh rho :
  OP.tau (OT.tr eta phi) =
  code_value rho (named_policy_formula true (named_bottom_expression (CEconst 0))
    depth_binder_policy (fun i => CEconst (eta i)) fresh (isolated_formula phi)).
Proof.
  rewrite <- (isolated_tr_named_policy phi eta _ fresh (fun i => eq_refl)).
  symmetry. apply isolated_named_expression_value.
Qed.

Lemma isolated_extensionality_exact :
  isolated_formula OldUndecidability.FOL.Sets.minZF.ax_ext' =
    Undecidability.FOL.Sets.minZF.ax_ext'.
Proof. reflexivity. Qed.

Lemma isolated_quoted_extensionality_exact :
  isolated_formula (OldK230S.KQuotFormula.qtrans (@OC.var OB.sig_empty 0)
      OldUndecidability.FOL.Sets.minZF.ax_ext') =
  source_qtrans (@C.var BinSig.sig_empty 0) Undecidability.FOL.Sets.minZF.ax_ext'.
Proof. reflexivity. Qed.

Print Assumptions isolated_named_expression_value.
Print Assumptions isolated_formula_depth.
Print Assumptions isolated_tr_named_policy.
Print Assumptions isolated_tr_code_value.
Print Assumptions isolated_extensionality_exact.
Print Assumptions isolated_quoted_extensionality_exact.
