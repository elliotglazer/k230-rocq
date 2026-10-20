(** The literal finite K bundle with native conjunction and existential.
    Opaque holes are decoded only by the genuine raw_source_image graph;
    named binders are closed by the actual raw binder map. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension
  CodeExpressions CodeDescent NumericalProofs ProofTemplates SetFormulaCodes SetCodeDescent
  SourceBounded SourceBoundMonotone SourceRenamingBounds NumericalRenaming RawBinderRenaming
  RawSourceImage RawSourceImageInversion RawSourceImageBounds RawSourcePropositional.
Unset Implicit Arguments.

Inductive native_named_template :=
| NNTHole : nat ->native_named_template
| NNTAtom : bool ->code_expr ->code_expr ->native_named_template
| NNTImpl : native_named_template ->native_named_template ->native_named_template
| NNTAnd : native_named_template ->native_named_template ->native_named_template
| NNTAll : code_expr ->native_named_template ->native_named_template
| NNTEx : code_expr ->native_named_template ->native_named_template.

Fixpoint native_named_raw_expression t :=match t with
  | NNTHole i=>CEvar i
  | NNTAtom eq a b=>if eq then E_weq a b else E_wel a b
  | NNTImpl a b=>E_wim (native_named_raw_expression a) (native_named_raw_expression b)
  | NNTAnd a b=>E_wa (native_named_raw_expression a) (native_named_raw_expression b)
  | NNTAll x a=>E_wal x (native_named_raw_expression a)
  | NNTEx x a=>E_wex x (native_named_raw_expression a)
  end.

Fixpoint native_named_evaluation M env t out :=match t with
  | NNTHole i=>raw_source_image M (env i) out
  | NNTAtom eq a b=>exists x y,code_relation M env a x /\code_relation M env b y /\
      sf_relation M (if eq then SFEqual else SFMember) x y out
  | NNTImpl a b=>exists x y,native_named_evaluation M env a x /\native_named_evaluation M env b y /\
      sf_relation M SFImpl x y out
  | NNTAnd a b=>exists x y,native_named_evaluation M env a x /\native_named_evaluation M env b y /\
      sf_relation M SFAnd x y out
  | NNTAll x a=>exists name body rb rc closed,code_relation M env x name /\
      native_named_evaluation M env a body /\raw_binder_renaming M name rb rc /\
      numerical_renaming M body rb rc (succM M name) (succM M (zeroM M)) closed /\
      sf_relation M SFAll closed (zeroM M) out
  | NNTEx x a=>exists name body rb rc closed,code_relation M env x name /\
      native_named_evaluation M env a body /\raw_binder_renaming M name rb rc /\
      numerical_renaming M body rb rc (succM M name) (succM M (zeroM M)) closed /\
      sf_relation M SFEx closed (zeroM M) out
  end.

(** Regularity is a checked property of the finite skeleton, not of any
    opaque matrix. Every primitive implication in K has a positive
    consequent, so the exceptional raw wim(0,0)=0 branch never occurs. *)
Fixpoint native_named_positive t :=match t with
  | NNTHole _=>false |NNTImpl a b=>orb (native_named_positive a) (native_named_positive b)
  | _=>true end.
Fixpoint native_named_regular t :=match t with
  | NNTHole _|NNTAtom _ _ _=>true
  | NNTImpl a b=>andb (andb (native_named_regular a) (native_named_regular b)) (native_named_positive b)
  | NNTAnd a b=>andb (native_named_regular a) (native_named_regular b)
  | NNTAll _ a|NNTEx _ a=>native_named_regular a end.

Theorem native_named_evaluation_total M env t :exists out,native_named_evaluation M env t out.
Proof.
  induction t as [i|eq a b|a IHa b IHb|a IHa b IHb|x a IH|x a IH];cbn [native_named_evaluation].
  - apply raw_source_image_total.
  - destruct (code_relation_total M a env) as (x&HX),(code_relation_total M b env) as (y&HY).
    destruct (sf_relation_total M (if eq then SFEqual else SFMember) x y) as (out&HO).
    exists out,x,y. auto.
  - destruct IHa as (x&HX),IHb as (y&HY),(sf_relation_total M SFImpl x y) as (out&HO).
    exists out,x,y. auto.
  - destruct IHa as (x&HX),IHb as (y&HY),(sf_relation_total M SFAnd x y) as (out&HO).
    exists out,x,y. auto.
  - destruct IH as (body&HB),(code_relation_total M x env) as (name&HN).
    destruct (raw_binder_renaming_total M name) as (rb&rc&HR).
    destruct (numerical_renaming_total M body rb rc (succM M name) (succM M (zeroM M))) as (closed&HC).
    destruct (sf_relation_total M SFAll closed (zeroM M)) as (out&HO).
    exists out,name,body,rb,rc,closed. repeat first [assumption|split].
  - destruct IH as (body&HB),(code_relation_total M x env) as (name&HN).
    destruct (raw_binder_renaming_total M name) as (rb&rc&HR).
    destruct (numerical_renaming_total M body rb rc (succM M name) (succM M (zeroM M))) as (closed&HC).
    destruct (sf_relation_total M SFEx closed (zeroM M)) as (out&HO).
    exists out,name,body,rb,rc,closed. repeat first [assumption|split].
Qed.

Theorem native_named_evaluation_bounded M env t :forall out,native_named_evaluation M env t out ->
  exists k,source_bounded M out k.
Proof.
  induction t as [i|eq a b|a IHa b IHb|a IHa b IHb|x a IH|x a IH];intros out HE;
    cbn [native_named_evaluation] in HE.
  - exact (raw_source_image_bounded M (env i) out HE).
  - destruct HE as (x&y&HX&HY&HO). exists (succM M (addM M x y)).
    apply (proj2 (source_bounded_accept_atom M (if eq then SFEqual else SFMember) x y out _
      ltac:(destruct eq;unfold sb_atomic;auto) HO)).
    split;[apply coding_le_add|rewrite (add_comm M x y);apply coding_le_add].
  - destruct HE as (x&y&HX&HY&HO). destruct (IHa x HX) as (k&HK),(IHb y HY) as (l&HL).
    exists (addM M k l). apply (proj2 (source_bounded_accept_binary M SFImpl x y out _
      ltac:(unfold sf_binary;auto) HO)). split.
    + exact (source_bounded_monotone M x k (addM M k l) HK (coding_le_add M k l)).
    + apply (source_bounded_monotone M y l (addM M k l) HL). rewrite (add_comm M k l). apply coding_le_add.
  - destruct HE as (x&y&HX&HY&HO). destruct (IHa x HX) as (k&HK),(IHb y HY) as (l&HL).
    exists (addM M k l). apply (proj2 (source_bounded_accept_binary M SFAnd x y out _
      ltac:(unfold sf_binary;auto) HO)). split.
    + exact (source_bounded_monotone M x k (addM M k l) HK (coding_le_add M k l)).
    + apply (source_bounded_monotone M y l (addM M k l) HL). rewrite (add_comm M k l). apply coding_le_add.
  - destruct HE as (name&body&rb&rc&closed&HN&HB&HR&HC&HO). destruct (IH body HB) as (k&HK).
    exists k. apply (proj2 (source_bounded_accept_unary M SFAll closed out k (or_introl eq_refl) HO)).
    exact (numerical_renaming_preserves_bound M body rb rc (succM M name) (succM M (zeroM M))
      closed k (succM M k) HK HC (raw_binder_maps_bound M name rb rc k HR)).
  - destruct HE as (name&body&rb&rc&closed&HN&HB&HR&HC&HO). destruct (IH body HB) as (k&HK).
    exists k. apply (proj2 (source_bounded_accept_unary M SFEx closed out k (or_intror eq_refl) HO)).
    exact (numerical_renaming_preserves_bound M body rb rc (succM M name) (succM M (zeroM M))
      closed k (succM M k) HK HC (raw_binder_maps_bound M name rb rc k HR)).
Qed.

Definition NNT_subset a b k :=NNTAll k (NNTImpl (NNTAtom false k a) (NNTAtom false k b)).
Definition NNT_request b k m :=NNTAll b (NNTImpl m (NNTEx b (NNTAnd m (NNTAtom false b k)))).
Definition NNT_core a b k m :=
  NNTEx k (NNTAnd (NNTImpl m (NNTAtom false b k))
    (NNTAll b (NNTImpl (NNTAtom false b k)
      (NNTEx a (NNTAnd m (NNTAll a (NNTImpl (NNT_subset a b k) (NNT_request b k m)))))))).
Definition NNT_vacuity a b c :=
  NNTAnd (NNTImpl (NNTAtom false a b) (NNTAll c (NNTAtom false a b)))
    (NNTImpl (NNTAtom true a b) (NNTAll c (NNTAtom true a b))).
Definition native_K_bundle_template :=NNTAnd
  (NNT_core (CEvar 0) (CEvar 1) (CEvar 2) (NNTHole 2))
  (NNT_vacuity (CEvar 0) (CEvar 1) (CEvar 2)).

Lemma native_K_bundle_literal :native_named_raw_expression native_K_bundle_template = code_bundle.
Proof. reflexivity. Qed.
Lemma native_K_bundle_regular :native_named_regular native_K_bundle_template = true.
Proof. reflexivity. Qed.

Print Assumptions native_named_evaluation_total.
Print Assumptions native_named_evaluation_bounded.
Print Assumptions native_K_bundle_literal.
