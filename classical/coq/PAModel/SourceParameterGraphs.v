(** Parameter compiler bounds and extensionality at the actual code graph. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SetCodeDescent
  SourceBounded SourceBoundedCalibration SourceFiniteParameters SourcePropositionalRebase SchemaConstructorBounds.
From FOL Require Import FullSyntax.
From Undecidability.FOL Require Import Syntax.Bounded Syntax.BinSig Sets.Signatures.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Theorem source_parameter_graph_ext {ff} M bound
    (phi:@Core.form sig_empty ZFSignature.ZF_pred_sig full_operators ff) :
  bounded bound phi ->forall names names' rho rho',
  (forall i x,(i<bound)%nat ->(code_relation M rho (names i) x <->code_relation M rho' (names' i) x)) ->
  forall f,code_relation M rho (source_parameter_expression names phi) f <->
    code_relation M rho' (source_parameter_expression names' phi) f.
Proof.
  intro HB. induction HB;intros names names' rho rho' HE f.
  - assert (HX:(sf_index (Vector.hd v)<n)%nat).
    { apply (proj1 (sb_term_bounded n (Vector.hd v)));apply H;rewrite (sb_vector_two v);now constructor. }
    assert (HY:(sf_index (Vector.hd (Vector.tl v))<n)%nat).
    { apply (proj1 (sb_term_bounded n (Vector.hd (Vector.tl v))));apply H;
      rewrite (sb_vector_two v);apply Vector.In_cons_tl;now constructor. }
    destruct P;cbn [source_parameter_expression].
    all: destruct (code_relation_total M (names (sf_index (Vector.hd v))) rho) as (x&HXG).
    all: destruct (code_relation_total M (names (sf_index (Vector.hd (Vector.tl v)))) rho) as (y&HYG).
    all: rewrite (schema_expression_graph M rho _ _ _ x y f HXG HYG),
      (schema_expression_graph M rho' _ _ _ x y f (proj1 (HE _ _ HX) HXG) (proj1 (HE _ _ HY) HYG));reflexivity.
  - cbn [source_parameter_expression].
    destruct (code_relation_total M (source_parameter_expression names phi) rho) as (x&HX).
    destruct (code_relation_total M (source_parameter_expression names psi) rho) as (y&HY).
    rewrite (schema_expression_graph M rho _ _ _ x y f HX HY),
      (schema_expression_graph M rho' _ _ _ x y f (proj1 (IHHB1 names names' rho rho' HE x) HX)
        (proj1 (IHHB2 names names' rho rho' HE y) HY)). reflexivity.
  - cbn [source_parameter_expression].
    assert (HLift:forall i x,(i<S n)%nat ->
      (code_relation M rho (source_parameter_up names i) x <->
       code_relation M rho' (source_parameter_up names' i) x)).
    { intros [|i] x HI;[reflexivity|]. cbn [source_parameter_up code_relation].
      setoid_rewrite (HE i _ ltac:(lia)). reflexivity. }
    destruct (code_relation_total M (source_parameter_expression (source_parameter_up names) phi) rho)
      as (x&HX).
    rewrite (schema_expression_graph M rho _ _ (CEconst 0) x (zeroM M) f HX eq_refl),
      (schema_expression_graph M rho' _ _ (CEconst 0) x (zeroM M) f
        (proj1 (IHHB (source_parameter_up names) (source_parameter_up names') rho rho' HLift x) HX) eq_refl).
    reflexivity.
  - reflexivity.
Qed.

Theorem source_parameter_graph_bounded {ff} M bound
    (phi:@Core.form sig_empty ZFSignature.ZF_pred_sig full_operators ff) :
  bounded bound phi ->forall names rho k,
  (forall i x,(i<bound)%nat ->code_relation M rho (names i) x ->coding_lt M x k) ->
  forall f,code_relation M rho (source_parameter_expression names phi) f ->source_bounded M f k.
Proof.
  intro HB. induction HB;intros names rho k HL f HF.
  - assert (HX:(sf_index (Vector.hd v)<n)%nat).
    { apply (proj1 (sb_term_bounded n (Vector.hd v)));apply H;rewrite (sb_vector_two v);now constructor. }
    assert (HY:(sf_index (Vector.hd (Vector.tl v))<n)%nat).
    { apply (proj1 (sb_term_bounded n (Vector.hd (Vector.tl v))));apply H;
      rewrite (sb_vector_two v);apply Vector.In_cons_tl;now constructor. }
    destruct P;cbn [source_parameter_expression] in HF.
    all: destruct (schema_expression_split M rho _ _ _ f HF) as (x&y&HXG&HYG&HAtom).
    + apply (proj2 (source_bounded_accept_atom M SFMember x y f k (or_introl eq_refl) HAtom)).
      split;[exact (HL _ _ HX HXG)|exact (HL _ _ HY HYG)].
    + apply (proj2 (source_bounded_accept_atom M SFEqual x y f k (or_intror eq_refl) HAtom)).
      split;[exact (HL _ _ HX HXG)|exact (HL _ _ HY HYG)].
  - cbn [source_parameter_expression] in HF.
    destruct (schema_expression_split M rho _ _ _ f HF) as (x&y&HX&HY&HAtom).
    assert (HH:sf_binary (match binop with Conj=>SFAnd|Disj=>SFOr|Impl=>SFImpl end)).
    { destruct binop;unfold sf_binary;auto. }
    apply (proj2 (source_bounded_accept_binary M _ x y f k HH HAtom)).
    split;[exact (IHHB1 names rho k HL x HX)|exact (IHHB2 names rho k HL y HY)].
  - cbn [source_parameter_expression] in HF.
    destruct (schema_expression_split M rho _ _ _ f HF) as (a&z&HA&HZ&HAll).
    change (z=zeroM M) in HZ. subst z.
    assert (HH:sf_unary (match quantop with All=>SFAll|Ex=>SFEx end)).
    { destruct quantop;unfold sf_unary;auto. }
    apply (proj2 (source_bounded_accept_unary M _ a f k HH HAll)).
    apply (IHHB (source_parameter_up names) rho (succM M k));[|exact HA].
    intros [|i] x HI HX;[change (x=zeroM M) in HX;subst x;apply coding_zero_lt_succ|].
    cbn [source_parameter_up code_relation] in HX. destruct HX as (old&one&HO&HE&EX).
    change (one=code_numeral M 1) in HE. subst one.
    pose proof (Arithmetic.succ_as_add M old) as ES.
    change (succM M old=addM M old (code_numeral M 1)) in ES. rewrite <- ES in EX. subst x.
    apply (proj2 (coding_lt_succ_cancel M old k)). exact (HL i old ltac:(lia) HO).
  - change (f=zeroM M) in HF. subst f. apply source_bounded_accept_falsity.
Qed.

Print Assumptions source_parameter_graph_ext.
Print Assumptions source_parameter_graph_bounded.
