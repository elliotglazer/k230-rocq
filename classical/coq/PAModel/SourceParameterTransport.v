(** Actual numerical substitution between two finite-formula parameter
    compilations. The free variable names themselves may be nonstandard. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SetCodeDescent
  SourceBoundedCalibration SourceFiniteParameters SourcePropositionalRebase
  SubstitutionSource NumericalSubstitutionMaps NumericalSubstitution.
From FOL Require Import FullSyntax.
From Undecidability.FOL Require Import Syntax.Bounded Syntax.BinSig Sets.Signatures.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Theorem source_parameter_transport {ff} M bound
    (phi:@Core.form sig_empty ZFSignature.ZF_pred_sig full_operators ff) :
  bounded bound phi ->forall names names' rho rho' b c n base f g,
  (forall i x y,(i<bound)%nat ->code_relation M rho (names i) x ->
    code_relation M rho' (names' i) y ->substitution_lookup M b c n base x y) ->
  code_relation M rho (source_parameter_expression names phi) f ->
  code_relation M rho' (source_parameter_expression names' phi) g ->
  numerical_substitution M f b c n base g.
Proof.
  intro HB. induction HB;intros names names' rho rho' b c n0 base f g HL HF HG.
  - assert (HX:(sf_index (Vector.hd v)<n)%nat).
    { apply (proj1 (sb_term_bounded n (Vector.hd v)));apply H;
      rewrite (sb_vector_two v);now constructor. }
    assert (HY:(sf_index (Vector.hd (Vector.tl v))<n)%nat).
    { apply (proj1 (sb_term_bounded n (Vector.hd (Vector.tl v))));apply H;
      rewrite (sb_vector_two v);apply Vector.In_cons_tl;now constructor. }
    destruct P;cbn [source_parameter_expression] in HF,HG.
    all: destruct (schema_expression_split M rho _ _ _ f HF) as (x&y&HXG&HYG&HAtom).
    all: destruct (schema_expression_split M rho' _ _ _ g HG) as (x'&y'&HXG'&HYG'&HAtom').
    + apply (proj2 (numerical_substitution_member M x y f b c n0 base g HAtom)).
      exists x',y'. split;[exact (HL _ _ _ HX HXG HXG')|].
      split;[exact (HL _ _ _ HY HYG HYG')|exact HAtom'].
    + apply (proj2 (numerical_substitution_equal M x y f b c n0 base g HAtom)).
      exists x',y'. split;[exact (HL _ _ _ HX HXG HXG')|].
      split;[exact (HL _ _ _ HY HYG HYG')|exact HAtom'].
  - cbn [source_parameter_expression] in HF,HG.
    destruct (schema_expression_split M rho _ _ _ f HF) as (x&y&HX&HY&HAtom).
    destruct (schema_expression_split M rho' _ _ _ g HG) as (x'&y'&HX'&HY'&HAtom').
    assert (HH:sf_binary (match binop with Conj=>SFAnd|Disj=>SFOr|Impl=>SFImpl end)).
    { destruct binop;unfold sf_binary;auto. }
    apply (proj2 (numerical_substitution_binary M _ x y f b c n0 base g HH HAtom)).
    exists x',y'. split;[exact (IHHB1 names names' rho rho' b c n0 base x x' HL HX HX')|].
    split;[exact (IHHB2 names names' rho rho' b c n0 base y y' HL HY HY')|exact HAtom'].
  - cbn [source_parameter_expression] in HF,HG.
    destruct (schema_expression_split M rho _ _ _ f HF) as (a&z&HA&HZ&HAll).
    destruct (schema_expression_split M rho' _ _ _ g HG) as (a'&z'&HA'&HZ'&HAll').
    change (z=zeroM M) in HZ. change (z'=zeroM M) in HZ'. subst z z'.
    destruct (substitution_lift_total M b c n0 base) as (d&e&m&HMap).
    assert (HLift:forall i x y,(i<S n)%nat ->
      code_relation M rho (source_parameter_up names i) x ->
      code_relation M rho' (source_parameter_up names' i) y ->
      substitution_lookup M d e m (succM M base) x y).
    { intros [|i] x y HI HXX HYY.
      - change (x=zeroM M) in HXX. change (y=zeroM M) in HYY. subst x y. exact (proj1 (proj2 HMap)).
      - cbn [source_parameter_up code_relation] in HXX,HYY.
        destruct HXX as (old&one&HOld&HOne&EX),HYY as (old'&one'&HOld'&HOne'&EY).
        change (one=code_numeral M 1) in HOne. change (one'=code_numeral M 1) in HOne'. subst one one'.
        change (x=addM M old (code_numeral M 1)) in EX.
        change (y=addM M old' (code_numeral M 1)) in EY.
        pose proof (Arithmetic.succ_as_add M old) as ES.
        change (succM M old=addM M old (code_numeral M 1)) in ES. rewrite <- ES in EX.
        pose proof (Arithmetic.succ_as_add M old') as ES'.
        change (succM M old'=addM M old' (code_numeral M 1)) in ES'. rewrite <- ES' in EY.
        subst x y. exact (proj2 (proj2 HMap) old old' (HL i old old' ltac:(lia) HOld HOld')). }
    pose proof (IHHB (source_parameter_up names) (source_parameter_up names') rho rho' d e m
      (succM M base) a a' HLift HA HA') as HS.
    destruct quantop.
    + apply (proj2 (numerical_substitution_quantifier M true a f b c n0 base g HAll)).
      exists d,e,m,a'. split;[exact HMap|]. split;assumption.
    + apply (proj2 (numerical_substitution_quantifier M false a f b c n0 base g HAll)).
      exists d,e,m,a'. split;[exact HMap|]. split;assumption.
  - change (f=zeroM M) in HF. change (g=zeroM M) in HG. subst f g.
    apply (proj2 (numerical_substitution_invalid M (zeroM M) b c n0 base (zeroM M)
      (or_introl eq_refl))). reflexivity.
Qed.

Print Assumptions source_parameter_transport.
