(** Literal correspondence of the legacy WF proof's minimal core axioms.
    ZFcl_min contains the ten unprefixed fixed axioms, and the closed
    universal closures of Separation and Replacement. *)
From PAModel Require Import OldNamedSyntaxBridge OldFullNDSourceBridge
  SetFormulaCodes NumericalCoreAxioms.
From OldRegCon Require MinZF.
From OldUndecidability.FOL.Syntax Require Facts.
From OldUndecidability.FOL.Sets Require minZF.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.
Module OM := OldUndecidability.FOL.Sets.minZF.
Module CM := Undecidability.FOL.Sets.minZF.
Module OF := OldUndecidability.FOL.Syntax.Facts.
Module CF := Undecidability.FOL.Syntax.Facts.

Lemma old_wf_core_fixed_exact :
  List.map isolated_formula OM.minZFeq'=CM.minZFeq'.
Proof. reflexivity. Qed.

Lemma old_wf_core_prefix_exact n (phi:isolated_old_form OC.falsity_on) :
  isolated_formula (OC.FullSyntax.forall_times n phi)=C.FullSyntax.forall_times n (isolated_formula phi).
Proof.
  induction n;[reflexivity|].
  change (C.quant C.FullSyntax.All (isolated_formula (OC.FullSyntax.forall_times n phi))=
    C.quant C.FullSyntax.All (C.FullSyntax.forall_times n (isolated_formula phi))).
  now rewrite IHn.
Qed.

Lemma old_wf_core_sep_exact (phi:isolated_old_form OC.falsity_on) :
  isolated_formula (OM.ax_sep' phi)=CM.ax_sep' (isolated_formula phi).
Proof.
  unfold OM.ax_sep',CM.ax_sep'. cbn [isolated_formula isolated_quant isolated_op isolated_atom].
  erewrite isolated_formula_subst with
    (tau:=fun i => match i with 0 => @C.var BinSig.sig_empty 0
      | S j => @C.var BinSig.sig_empty (3+j) end).
  - reflexivity.
  - intros [|i];reflexivity.
Qed.

Lemma old_wf_core_rep_exact (phi:isolated_old_form OC.falsity_on) :
  isolated_formula (OM.ax_rep' phi)=CM.ax_rep' (isolated_formula phi).
Proof.
  unfold OM.ax_rep',OM.fun_rel',CM.ax_rep',CM.fun_rel'.
  cbn [isolated_formula isolated_quant isolated_op isolated_atom].
  erewrite isolated_formula_subst with
    (tau:=fun i => match i with 0 => @C.var BinSig.sig_empty 2
      | 1 => @C.var BinSig.sig_empty 1 | S(S j) => @C.var BinSig.sig_empty (3+j) end).
  2:{ intros [|[|i]];reflexivity. }
  erewrite isolated_formula_subst with
    (tau:=fun i => match i with 0 => @C.var BinSig.sig_empty 2
      | 1 => @C.var BinSig.sig_empty 0 | S(S j) => @C.var BinSig.sig_empty (3+j) end).
  2:{ intros [|[|i]];reflexivity. }
  erewrite isolated_formula_subst with
    (tau:=fun i => match i with 0 => @C.var BinSig.sig_empty 0
      | 1 => @C.var BinSig.sig_empty 1 | S(S j) => @C.var BinSig.sig_empty (4+j) end).
  2:{ intros [|[|i]];reflexivity. }
  reflexivity.
Qed.

Theorem old_wf_minimal_core_exact phi : OldRegCon.MinZF.ZFcl_min phi ->
  standard_zfc_core_source_axiom (isolated_formula phi).
Proof.
  intros [HF|[HS|HR]].
  - left. rewrite <-old_wf_core_fixed_exact. apply List.in_map. exact HF.
  - destruct HS as [n [body [-> HB]]]. right;left.
    exists (isolated_formula body),n. split.
    + rewrite old_wf_core_prefix_exact,old_wf_core_sep_exact. reflexivity.
    + exact (isolated_bounded 0 _ HB).
  - destruct HR as [n [body [-> HB]]]. right;right.
    exists (isolated_formula body),n. split.
    + rewrite old_wf_core_prefix_exact,old_wf_core_rep_exact. reflexivity.
    + exact (isolated_bounded 0 _ HB).
Qed.

Print Assumptions old_wf_core_fixed_exact.
Print Assumptions old_wf_core_sep_exact.
Print Assumptions old_wf_core_rep_exact.
Print Assumptions old_wf_minimal_core_exact.
