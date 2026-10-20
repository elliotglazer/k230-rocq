(** A proof bridge from the import-isolated original finite FullND calculus.
    This only lifts fixed external proofs. Arbitrary internal source proofs
    are handled by SourceRelativeFullTranslation instead. *)
From PAModel Require Import OldNamedSyntaxBridge SetFormulaCodes SourceNumeralLift
  Model FiniteCoding CodeExpressions NumericalSourceFull SourceFiniteContexts.
From OldUndecidability.FOL Require Syntax.Core Syntax.BinSig Sets.Signatures Deduction.FullND.
From Undecidability.FOL Require Import Syntax.Core Syntax.BinSig Sets.Signatures Deduction.FullND.
From OldUndecidability.FOL.Syntax Require Bounded.
From Undecidability.FOL.Syntax Require Import Bounded.
From Stdlib Require Import Lists.List Vectors.Vector.
Module OBound := OldUndecidability.FOL.Syntax.Bounded.
Module CBound := Undecidability.FOL.Syntax.Bounded.
Module O := OldUndecidability.FOL.Syntax.Core.
Module C := Undecidability.FOL.Syntax.Core.
Module OND := OldUndecidability.FOL.Deduction.FullND.
Module CND := Undecidability.FOL.Deduction.FullND.
Module OS := OldUndecidability.FOL.Sets.Signatures.
Module CS := Undecidability.FOL.Sets.Signatures.
Definition old_peirce p := match p with O.class=>C.class | O.intu=>C.intu end.
Definition new_term := sf_term.
Unset Implicit Arguments.
Lemma isolated_old_term_subst sigma t : isolated_term (O.subst_term sigma t) =
 C.subst_term (fun i => isolated_term (sigma i)) (isolated_term t).
Proof. destruct t as [i|[]]; reflexivity. Qed.

Lemma old_up_match sigma tau :
 (forall i,isolated_term (sigma i)=tau i) ->
 forall i, isolated_term (O.up sigma i)=C.up tau i.
Proof.
 intros H [|i]; [reflexivity|]. cbn [O.up C.up O.scons C.scons O.funcomp C.funcomp].
 unfold O.funcomp,C.funcomp. rewrite isolated_old_term_subst. rewrite H. reflexivity.
Qed.

Lemma old_vector_subst n (v:Vector.t isolated_old_term n) : forall sigma tau,
 (forall i,isolated_term (sigma i)=tau i) ->
 Vector.map isolated_term (Vector.map (O.subst_term sigma) v) =
 Vector.map (C.subst_term tau) (Vector.map isolated_term v).
Proof.
 induction v as [|t n v IH]; intros sigma tau H; cbn; [reflexivity|].
 f_equal; [rewrite isolated_old_term_subst;destruct t as [i|[]];apply H|apply IH;exact H].
Qed.

Lemma isolated_formula_subst {ff} (phi:isolated_old_form ff) : forall sigma tau,
 (forall i,isolated_term (sigma i)=tau i) ->
 isolated_formula (O.subst_form sigma phi)=C.subst_form tau (isolated_formula phi).
Proof.
 induction phi as [|ff p v|ff op a IHa b IHb|ff q a IH]; intros sigma tau H.
 - reflexivity.
 - destruct p; cbn [O.subst_form C.subst_form isolated_formula isolated_atom].
   all: f_equal; apply old_vector_subst; exact H.
 - cbn [O.subst_form C.subst_form isolated_formula]. rewrite (IHa sigma tau H),(IHb sigma tau H). reflexivity.
 - cbn [O.subst_form C.subst_form isolated_formula]. rewrite (IH (O.up sigma) (C.up tau) (old_up_match sigma tau H)). reflexivity.
Qed.

Definition old_shift := fun i => @O.var OldUndecidability.FOL.Syntax.BinSig.sig_empty (S i).
Definition new_shift := fun i => @C.var BinSig.sig_empty (S i).

Lemma isolated_old_formula_shift {ff} (phi:isolated_old_form ff) :
 isolated_formula (O.subst_form old_shift phi) = C.subst_form new_shift (isolated_formula phi).
Proof. apply isolated_formula_subst. intro i. reflexivity. Qed.

Lemma old_context_shift {ff} (A:list(isolated_old_form ff)) :
 List.map isolated_formula (List.map (O.subst_form old_shift) A) =
 List.map (C.subst_form new_shift) (List.map isolated_formula A).
Proof. rewrite !List.map_map. apply List.map_ext. intro phi. apply isolated_old_formula_shift. Qed.

Lemma isolated_old_formula_instantiate {ff} (phi:isolated_old_form ff) t :
 isolated_formula (O.subst_form (O.scons t O.var) phi) =
 C.subst_form (C.scons (isolated_term t) C.var) (isolated_formula phi).
Proof. apply isolated_formula_subst. intros [|i]; reflexivity. Qed.

Theorem isolated_fullnd_to_current {ff p} (A:list(isolated_old_form ff)) phi :
 @OND.prv OldUndecidability.FOL.Syntax.BinSig.sig_empty OS.ZFSignature.ZF_pred_sig ff p A phi ->
 @CND.prv BinSig.sig_empty CS.ZFSignature.ZF_pred_sig (isolated_flag ff) (old_peirce p)
   (List.map isolated_formula A) (isolated_formula phi).
Proof.
 intro H. induction H as
 [ff p A a d H IH
 |ff p A a d H1 IH1 H2 IH2
 |ff p A a H IH
 |ff p A t a H IH
 |ff p A t a H IH
 |ff p A a d H1 IH1 H2 IH2
 |p A a H IH
 |ff p A a Hin
 |ff p A a d H1 IH1 H2 IH2
 |ff p A a d H IH
 |ff p A a d H IH
 |ff p A a d H IH
 |ff p A a d H IH
 |ff p A a d f H0 IH0 H1 IH1 H2 IH2
 |ff A a d]; cbn [isolated_formula isolated_op isolated_quant isolated_flag old_peirce List.map] in *.
 - apply CND.II. exact IH.
 - eapply CND.IE; [exact IH1|exact IH2].
 - apply CND.AllI. rewrite old_context_shift in IH. exact IH.
 - rewrite isolated_old_formula_instantiate. apply CND.AllE. exact IH.
 - apply CND.ExI with (t:=isolated_term t). rewrite isolated_old_formula_instantiate in IH. exact IH.
 - eapply CND.ExE; [exact IH1|]. rewrite old_context_shift,isolated_old_formula_shift in IH2. exact IH2.
 - apply CND.Exp. exact IH.
 - apply CND.Ctx. apply List.in_map. exact Hin.
 - apply CND.CI; assumption.
 - eapply CND.CE1; exact IH.
 - eapply CND.CE2; exact IH.
 - apply CND.DI1; exact IH.
 - apply CND.DI2; exact IH.
 - eapply CND.DE; [exact IH0|exact IH1|exact IH2].
 - apply CND.Pc.
Qed.




Print Assumptions isolated_fullnd_to_current.

Lemma isolated_vector_map_member {A B} (f:A->B) n (v:Vector.t A n) y :
 Vector.In y (Vector.map f v) -> exists x, f x = y /\ Vector.In x v.
Proof.
 intro H. apply Vector.to_list_In in H.
 rewrite Vector.to_list_map in H. apply List.in_map_iff in H.
 destruct H as [x [Hx Hin]]. exists x. split; [exact Hx|].
 apply Vector.to_list_In. exact Hin.
Qed.

Lemma isolated_old_term_bounded n (t:isolated_old_term) :
 @OBound.bounded_t OldUndecidability.FOL.Syntax.BinSig.sig_empty n t ->
 @CBound.bounded_t BinSig.sig_empty n (isolated_term t).
Proof. destruct t as [i|[]]. intro H. inversion H; subst. constructor. assumption. Qed.

Theorem isolated_bounded {ff} n (phi:isolated_old_form ff) :
 OBound.bounded n phi -> CBound.bounded n (isolated_formula phi).
Proof.
 intro H. induction H.
 - destruct P; cbn [isolated_formula isolated_atom]; constructor; intros t Ht;
   destruct (isolated_vector_map_member isolated_term _ v t Ht) as [x [<- Hx]];
   apply isolated_old_term_bounded; apply H; exact Hx.
 - cbn [isolated_formula]. constructor; assumption.
 - cbn [isolated_formula]. constructor; assumption.
 - cbn [isolated_formula]. constructor.
Qed.


Theorem isolated_fullnd_forward_model {ff p} M (A:list(isolated_old_form ff)) phi :
  @OND.prv OldUndecidability.FOL.Syntax.BinSig.sig_empty OS.ZFSignature.ZF_pred_sig ff p A phi ->
  forall b c n,source_model_context_represents M b c n (List.map isolated_formula A) ->
    source_full_prv M b c n (code_numeral M (sf_encode (isolated_formula phi))).
Proof.
  intro H. exact (@source_full_forward_model (isolated_flag ff) (old_peirce p) M
    (List.map isolated_formula A) (isolated_formula phi)
    (@isolated_fullnd_to_current ff p A phi H)).
Qed.
Print Assumptions isolated_bounded.
Print Assumptions isolated_fullnd_forward_model.
