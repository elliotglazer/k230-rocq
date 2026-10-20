(** Reuse the finite named-template syntax for arbitrary source-code holes.
 Only the finite outer template is traversed. Hole formulas and all variable
 names may be nonstandard PA-model elements. No raw decoder is involved. *)
From Stdlib Require Import List.
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension CodeExpressions SetFormulaCodes SetCodeDescent
 SourceBounded SourceBoundMonotone SourceRenamingBounds NumericalRenamingMaps NumericalRenaming
 RawBinderRenaming SourceNamedSelfSpecialization NativeKBundle SourceNamedScopes SourceNamedScopeBinding NativeNamedScopeEvaluation.
Import ListNotations.
Unset Implicit Arguments.
Fixpoint source_hole_named_evaluation M env holes t out :=match t with
  | NNTHole i=>out=holes i
  | NNTAtom eq a b=>exists x y,code_relation M env a x /\code_relation M env b y /\
      sf_relation M (if eq then SFEqual else SFMember) x y out
  | NNTImpl a b=>exists x y,source_hole_named_evaluation M env holes a x /\source_hole_named_evaluation M env holes b y /\
      sf_relation M SFImpl x y out
  | NNTAnd a b=>exists x y,source_hole_named_evaluation M env holes a x /\source_hole_named_evaluation M env holes b y /\
      sf_relation M SFAnd x y out
  | NNTAll x a=>exists name body rb rc closed,code_relation M env x name /\
      source_hole_named_evaluation M env holes a body /\raw_binder_renaming M name rb rc /\
      numerical_renaming M body rb rc (succM M name) (succM M (zeroM M)) closed /\
      sf_relation M SFAll closed (zeroM M) out
  | NNTEx x a=>exists name body rb rc closed,code_relation M env x name /\
      source_hole_named_evaluation M env holes a body /\raw_binder_renaming M name rb rc /\
      numerical_renaming M body rb rc (succM M name) (succM M (zeroM M)) closed /\
      sf_relation M SFEx closed (zeroM M) out
  end.

Theorem source_hole_named_evaluation_total M env holes t :exists out,source_hole_named_evaluation M env holes t out.
Proof.
  induction t as [i|eq a b|a IHa b IHb|a IHa b IHb|x a IH|x a IH];cbn [source_hole_named_evaluation].
  - exists(holes i). reflexivity.
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

Theorem source_hole_named_evaluation_bounded M env holes t :(forall i,exists k,source_bounded M(holes i)k) ->forall out,source_hole_named_evaluation M env holes t out ->
  exists k,source_bounded M out k.
Proof.
  intro HHoles. induction t as [i|eq a b|a IHa b IHb|a IHa b IHb|x a IH|x a IH];intros out HE;
    cbn [source_hole_named_evaluation] in HE.
  - subst out. exact(HHoles i).
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
    exact(source_named_closure_bounded M body name rb rc closed k HK HR HC).
  - destruct HE as (name&body&rb&rc&closed&HN&HB&HR&HC&HO). destruct (IH body HB) as (k&HK).
    exists k. apply (proj2 (source_bounded_accept_unary M SFEx closed out k (or_intror eq_refl) HO)).
    exact(source_named_closure_bounded M body name rb rc closed k HK HR HC).
Qed.

Fixpoint scoped_source_hole_evaluation M env holes names t out :=match t with
  | NNTHole i=>named_scope_renaming M names(holes i)out
  | NNTAtom eq a b=>exists x y u v,code_relation M env a x /\code_relation M env b y /\
      named_scope_index M names x u /\named_scope_index M names y v /\
      sf_relation M (if eq then SFEqual else SFMember) u v out
  | NNTImpl a b=>exists x y,scoped_source_hole_evaluation M env holes names a x /\
      scoped_source_hole_evaluation M env holes names b y /\sf_relation M SFImpl x y out
  | NNTAnd a b=>exists x y,scoped_source_hole_evaluation M env holes names a x /\
      scoped_source_hole_evaluation M env holes names b y /\sf_relation M SFAnd x y out
  | NNTAll x a=>exists name body,code_relation M env x name /\
      scoped_source_hole_evaluation M env holes (name::names) a body /\sf_relation M SFAll body (zeroM M) out
  | NNTEx x a=>exists name body,code_relation M env x name /\
      scoped_source_hole_evaluation M env holes (name::names) a body /\sf_relation M SFEx body (zeroM M) out
  end.

Theorem source_hole_named_scope_evaluation M env holes t :(forall i,exists k,source_bounded M(holes i)k) ->forall original names,
  source_hole_named_evaluation M env holes t original ->exists result,
    scoped_source_hole_evaluation M env holes names t result /\named_scope_renaming M names original result.
Proof.
  intro HHoles. induction t as [i|eq a b|a IHA b IHB|a IHA b IHB|x a IH|x a IH];
    intros original names HE;cbn [source_hole_named_evaluation] in HE.
  - subst original. destruct(named_scope_renaming_total M names(holes i))as(result&HR).
    exists result. exact(conj HR HR).
  - destruct HE as (x&y&HX&HY&HO).
    destruct (named_scope_index_total M names x) as (u&HU),
      (named_scope_index_total M names y) as (v&HV).
    destruct (sf_relation_total M (if eq then SFEqual else SFMember) u v) as (result&HR).
    destruct (named_scope_map_total M names) as (rb&rc&HM).
    exists result. split.
    + exists x,y,u,v. repeat first [assumption|split].
    + exists rb,rc. split;[exact HM|]. destruct eq.
      * apply (proj2 (numerical_renaming_equal M x y original rb rc _ _ result HO)).
        exists u,v. split;[now apply HM|]. split;[now apply HM|exact HR].
      * apply (proj2 (numerical_renaming_member M x y original rb rc _ _ result HO)).
        exists u,v. split;[now apply HM|]. split;[now apply HM|exact HR].
  - destruct HE as (x&y&HX&HY&HO).
    destruct (IHA x names HX) as (u&HU&HRU),(IHB y names HY) as (v&HV&HRV).
    destruct (sf_relation_total M SFImpl u v) as (result&HR).
    destruct (named_scope_map_total M names) as (rb&rc&HM).
    exists result. split;[exists u,v;repeat first [assumption|split]|].
    exists rb,rc. split;[exact HM|].
    apply (proj2 (numerical_renaming_binary M SFImpl x y original rb rc _ _ result
      ltac:(unfold sf_binary;auto) HO)).
    exists u,v. split;[exact (named_scope_renaming_at M names x u rb rc HRU HM)|].
    split;[exact (named_scope_renaming_at M names y v rb rc HRV HM)|exact HR].
  - destruct HE as (x&y&HX&HY&HO).
    destruct (IHA x names HX) as (u&HU&HRU),(IHB y names HY) as (v&HV&HRV).
    destruct (sf_relation_total M SFAnd u v) as (result&HR).
    destruct (named_scope_map_total M names) as (rb&rc&HM).
    exists result. split;[exists u,v;repeat first [assumption|split]|].
    exists rb,rc. split;[exact HM|].
    apply (proj2 (numerical_renaming_binary M SFAnd x y original rb rc _ _ result
      ltac:(unfold sf_binary;auto) HO)).
    exists u,v. split;[exact (named_scope_renaming_at M names x u rb rc HRU HM)|].
    split;[exact (named_scope_renaming_at M names y v rb rc HRV HM)|exact HR].
  - destruct HE as (name&body&ab&ac&closed&HN&HB&HX&HC&HO).
    destruct (IH body (name::names) HB) as (target&HT&HR).
    destruct (sf_relation_total M SFAll target (zeroM M)) as (result&HResult).
    destruct (source_hole_named_evaluation_bounded M env holes a HHoles body HB) as (k&HK).
    exists result. split;[exists name,target;auto|].
    exact (named_scope_quantifier_transport M names name body closed original target result ab ac SFAll k
      (or_introl eq_refl) HK HX HC HO HR HResult).
  - destruct HE as (name&body&ab&ac&closed&HN&HB&HX&HC&HO).
    destruct (IH body (name::names) HB) as (target&HT&HR).
    destruct (sf_relation_total M SFEx target (zeroM M)) as (result&HResult).
    destruct (source_hole_named_evaluation_bounded M env holes a HHoles body HB) as (k&HK).
    exists result. split;[exists name,target;auto|].
    exact (named_scope_quantifier_transport M names name body closed original target result ab ac SFEx k
      (or_intror eq_refl) HK HX HC HO HR HResult).
Qed.

Theorem scoped_source_hole_evaluation_functional M env holes t :forall names a b,
  scoped_source_hole_evaluation M env holes names t a ->scoped_source_hole_evaluation M env holes names t b ->a=b.
Proof.
  induction t as [i|eq x y|x IHX y IHY|x IHX y IHY|x a IH|x a IH];
    intros names a0 b0 HLeft HRight;cbn [scoped_source_hole_evaluation] in HLeft,HRight.
  - exact(named_scope_renaming_functional M names(holes i)a0 b0 HLeft HRight).
  - destruct HLeft as (a&b&u&v&HA&HB&HU&HV&HO),HRight as (a'&b'&u'&v'&HA'&HB'&HU'&HV'&HO').
    pose proof (code_relation_functional M x env a a' HA HA') as EA.
    pose proof (code_relation_functional M y env b b' HB HB') as EB. subst a' b'.
    pose proof (named_scope_index_functional M names a u u' HU HU') as EU.
    pose proof (named_scope_index_functional M names b v v' HV HV') as EV. subst u' v'.
    exact (sf_relation_functional M (if eq then SFEqual else SFMember) u v a0 b0 HO HO').
  - destruct HLeft as (a&b&HA&HB&HO),HRight as (a'&b'&HA'&HB'&HO').
    pose proof (IHX names a a' HA HA') as EA. pose proof (IHY names b b' HB HB') as EB. subst a' b'.
    exact (sf_relation_functional M SFImpl a b a0 b0 HO HO').
  - destruct HLeft as (a&b&HA&HB&HO),HRight as (a'&b'&HA'&HB'&HO').
    pose proof (IHX names a a' HA HA') as EA. pose proof (IHY names b b' HB HB') as EB. subst a' b'.
    exact (sf_relation_functional M SFAnd a b a0 b0 HO HO').
  - destruct HLeft as (name&body&HN&HB&HO),HRight as (name'&body'&HN'&HB'&HO').
    pose proof (code_relation_functional M x env name name' HN HN') as EN. subst name'.
    pose proof (IH (name::names) body body' HB HB') as EB. subst body'.
    exact (sf_relation_functional M SFAll body (zeroM M) a0 b0 HO HO').
  - destruct HLeft as (name&body&HN&HB&HO),HRight as (name'&body'&HN'&HB'&HO').
    pose proof (code_relation_functional M x env name name' HN HN') as EN. subst name'.
    pose proof (IH (name::names) body body' HB HB') as EB. subst body'.
    exact (sf_relation_functional M SFEx body (zeroM M) a0 b0 HO HO').
Qed.

Theorem source_hole_named_scope_empty_exact M env holes t f :
  (forall i,exists k,source_bounded M(holes i)k) ->
  source_hole_named_evaluation M env holes t f ->scoped_source_hole_evaluation M env holes [] t f.
Proof.
  intros HHoles HF. destruct (source_hole_named_scope_evaluation M env holes t HHoles f [] HF) as (g&HG&HR).
  destruct (source_hole_named_evaluation_bounded M env holes t HHoles f HF) as (k&HK).
  pose proof (named_scope_renaming_empty M f g k HK HR) as E. now subst g.
Qed.

Print Assumptions source_hole_named_scope_evaluation.
Print Assumptions source_hole_named_scope_empty_exact.
