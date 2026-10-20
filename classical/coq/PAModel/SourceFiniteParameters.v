(** Fixed finite source formulas with model-valued free variable names.
    Binders still use genuine de Bruijn lifting. The adapter constructs
    the actual internally coded renaming, not a semantic interpretation. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
  SetFormulaCodes SetCodeDescent ZFCFiniteSourceCodes SourceNumeralLift
  NumericalRenamingMaps NumericalRenaming SubstitutionSource.
From FOL Require Import FullSyntax.
From Undecidability.FOL Require Import Syntax.BinSig Sets.Signatures.
Unset Implicit Arguments.

Definition source_parameter_up (names:nat->code_expr) i :=
  match i with 0=>CEconst 0 | S j=>CEadd (names j) (CEconst 1) end.

Fixpoint source_parameter_expression {ff}
    (names:nat->code_expr)
    (phi:@Core.form sig_empty ZFSignature.ZF_pred_sig full_operators ff) : code_expr :=
  match phi with
  | falsity=>CEconst 0
  | atom P v=>
    match P return Vector.t sf_term (ZF_pred_ar P)->code_expr with
    | elem=>fun v=>E_sf SFMember (names (sf_index (Vector.hd v)))
        (names (sf_index (Vector.hd (Vector.tl v))))
    | equal=>fun v=>E_sf SFEqual (names (sf_index (Vector.hd v)))
        (names (sf_index (Vector.hd (Vector.tl v))))
    end v
  | bin op a b=>E_sf
      (match op with Conj=>SFAnd | Disj=>SFOr | Impl=>SFImpl end)
      (source_parameter_expression names a) (source_parameter_expression names b)
  | quant q a=>E_sf (match q with All=>SFAll | Ex=>SFEx end)
      (source_parameter_expression (source_parameter_up names) a) (CEconst 0)
  end.

Theorem source_finite_parameter_renaming {ff} M
    (phi:@Core.form sig_empty ZFSignature.ZF_pred_sig full_operators ff) :
  forall names rho eb c n delta out,
  (forall i x,code_relation M rho (names i) x ->
    renaming_lookup M eb c n delta (code_numeral M i) x) ->
  code_relation M rho (source_parameter_expression names phi) out ->
  numerical_renaming M (code_numeral M (sf_encode phi)) eb c n delta out.
Proof.
  induction phi;
    intros names rho eb c n delta out HL HO.
  - change (out=zeroM M) in HO. subst out.
    apply (proj2 (numerical_renaming_invalid M (zeroM M) eb c n delta (zeroM M)
      (or_introl eq_refl))). reflexivity.
  - destruct (code_relation_total M (names (sf_index (Vector.hd t))) rho) as [x HX].
    destruct (code_relation_total M (names (sf_index (Vector.hd (Vector.tl t)))) rho) as [y HY].
    destruct P.
    + apply (proj2 (numerical_renaming_member M _ _ _ eb c n delta out
        (sf_make_numeral M SFMember _ _))).
      exists x,y. split;[exact (HL _ _ HX)|]. split;[exact (HL _ _ HY)|].
      exact (proj1 (substitution_source_constructor_graph M rho SFMember _ _ x y out HX HY) HO).
    + apply (proj2 (numerical_renaming_equal M _ _ _ eb c n delta out
        (sf_make_numeral M SFEqual _ _))).
      exists x,y. split;[exact (HL _ _ HX)|]. split;[exact (HL _ _ HY)|].
      exact (proj1 (substitution_source_constructor_graph M rho SFEqual _ _ x y out HX HY) HO).
  - destruct (code_relation_total M (source_parameter_expression names phi1) rho) as [x HX].
    destruct (code_relation_total M (source_parameter_expression names phi2) rho) as [y HY].
    pose proof (IHphi1 names rho eb c n delta x HL HX) as RX.
    pose proof (IHphi2 names rho eb c n delta y HL HY) as RY.
    destruct b0.
    + apply (proj2 (numerical_renaming_binary M SFAnd _ _ _ eb c n delta out
        ltac:(unfold sf_binary;auto) (sf_make_numeral M SFAnd _ _))).
      exists x,y. split;[exact RX|]. split;[exact RY|].
      exact (proj1 (substitution_source_constructor_graph M rho SFAnd _ _ x y out HX HY) HO).
    + apply (proj2 (numerical_renaming_binary M SFOr _ _ _ eb c n delta out
        ltac:(unfold sf_binary;auto) (sf_make_numeral M SFOr _ _))).
      exists x,y. split;[exact RX|]. split;[exact RY|].
      exact (proj1 (substitution_source_constructor_graph M rho SFOr _ _ x y out HX HY) HO).
    + apply (proj2 (numerical_renaming_binary M SFImpl _ _ _ eb c n delta out
        ltac:(unfold sf_binary;auto) (sf_make_numeral M SFImpl _ _))).
      exists x,y. split;[exact RX|]. split;[exact RY|].
      exact (proj1 (substitution_source_constructor_graph M rho SFImpl _ _ x y out HX HY) HO).
  - destruct (renaming_lift_total M eb c n delta) as (rb&rc&rn&HMap).
    destruct (code_relation_total M (source_parameter_expression (source_parameter_up names) phi) rho)
      as [body HBody].
    assert (HLift:forall i x,code_relation M rho (source_parameter_up names i) x ->
      renaming_lookup M rb rc rn delta (code_numeral M i) x).
    { intros [|i] x HX.
      - change (x=zeroM M) in HX. subst x. exact (proj1 (proj2 HMap)).
      - cbn [source_parameter_up code_relation] in HX.
        destruct HX as (old&one&HOld&HE&HX). change (one=code_numeral M 1) in HE.
        subst one. change (x=addM M old (code_numeral M 1)) in HX. pose proof (Arithmetic.succ_as_add M old) as ES. change (succM M old=addM M old (code_numeral M 1)) in ES. rewrite <-ES in HX. subst x.
        exact (proj2 (proj2 HMap) (code_numeral M i) old (HL i old HOld)). }
    pose proof (IHphi (source_parameter_up names) rho rb rc rn delta body HLift HBody) as RBody.
    destruct q.
    + apply (proj2 (numerical_renaming_quantifier M true _ _ eb c n delta out
        (sf_make_numeral M SFAll _ 0))).
      exists rb,rc,rn,body. split;[exact HMap|]. split;[exact RBody|].
      exact (proj1 (substitution_source_constructor_graph M rho SFAll _ (CEconst 0)
        body (zeroM M) out HBody eq_refl) HO).
    + apply (proj2 (numerical_renaming_quantifier M false _ _ eb c n delta out
        (sf_make_numeral M SFEx _ 0))).
      exists rb,rc,rn,body. split;[exact HMap|]. split;[exact RBody|].
      exact (proj1 (substitution_source_constructor_graph M rho SFEx _ (CEconst 0)
        body (zeroM M) out HBody eq_refl) HO).
Qed.

Print Assumptions source_finite_parameter_renaming.




