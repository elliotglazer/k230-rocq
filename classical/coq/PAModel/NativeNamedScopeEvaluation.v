(** The existing finite named K template evaluated by explicit binder
    scopes. Only its finitely many opaque matrix occurrences undergo
    arithmetic renaming. No recursion on a standard matrix representation
    and no assumption about which names occur in a matrix is used. *)
From Stdlib Require Import List.
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  SetFormulaCodes SetCodeDescent SourceBounded NumericalRenamingMaps NumericalRenaming
  RawBinderRenaming RawSourceImage RawSourceImageInversion NativeKBundle
  SourceNamedScopes SourceNamedScopeBinding.
Import ListNotations.
Unset Implicit Arguments.

Fixpoint scoped_native_evaluation M env names t out :=match t with
  | NNTHole i=>exists f,raw_source_image M (env i) f /\named_scope_renaming M names f out
  | NNTAtom eq a b=>exists x y u v,code_relation M env a x /\code_relation M env b y /\
      named_scope_index M names x u /\named_scope_index M names y v /\
      sf_relation M (if eq then SFEqual else SFMember) u v out
  | NNTImpl a b=>exists x y,scoped_native_evaluation M env names a x /\
      scoped_native_evaluation M env names b y /\sf_relation M SFImpl x y out
  | NNTAnd a b=>exists x y,scoped_native_evaluation M env names a x /\
      scoped_native_evaluation M env names b y /\sf_relation M SFAnd x y out
  | NNTAll x a=>exists name body,code_relation M env x name /\
      scoped_native_evaluation M env (name::names) a body /\sf_relation M SFAll body (zeroM M) out
  | NNTEx x a=>exists name body,code_relation M env x name /\
      scoped_native_evaluation M env (name::names) a body /\sf_relation M SFEx body (zeroM M) out
  end.

Lemma named_scope_quantifier_transport M names name body closed original target result ab ac h k :
  (h=SFAll \/h=SFEx) ->source_bounded M body k ->
  raw_binder_renaming M name ab ac ->
  numerical_renaming M body ab ac (succM M name) (code_numeral M 1) closed ->
  sf_relation M h closed (zeroM M) original ->
  named_scope_renaming M (name::names) body target ->sf_relation M h target (zeroM M) result ->
  named_scope_renaming M names original result.
Proof.
  intros HH HB HX HC HO (cb&cc&HM&HT) HResult.
  destruct (named_scope_map_total M names) as (rb&rc&HR).
  destruct (renaming_lift_total M rb rc (named_scope_bound M names)
    (code_numeral M (length names))) as (db&dc&dn&HL).
  pose proof (named_scope_bind_lift M names name body closed target rb rc ab ac db dc dn cb cc k
    HB HR HX HC HL HM HT) as HClosed.
  exists rb,rc. split;[exact HR|].
  destruct HH as [EH|EH];subst h.
  - apply (proj2 (numerical_renaming_quantifier M true closed original rb rc _ _ result HO)).
    exists db,dc,dn,target. auto.
  - apply (proj2 (numerical_renaming_quantifier M false closed original rb rc _ _ result HO)).
    exists db,dc,dn,target. auto.
Qed.

Theorem native_named_scope_evaluation M env t :forall original names,
  native_named_evaluation M env t original ->exists result,
    scoped_native_evaluation M env names t result /\named_scope_renaming M names original result.
Proof.
  induction t as [i|eq a b|a IHA b IHB|a IHA b IHB|x a IH|x a IH];
    intros original names HE;cbn [native_named_evaluation] in HE.
  - destruct (named_scope_renaming_total M names original) as (result&HR).
    exists result. split;[exists original;auto|exact HR].
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
    destruct (native_named_evaluation_bounded M env a body HB) as (k&HK).
    exists result. split;[exists name,target;auto|].
    exact (named_scope_quantifier_transport M names name body closed original target result ab ac SFAll k
      (or_introl eq_refl) HK HX HC HO HR HResult).
  - destruct HE as (name&body&ab&ac&closed&HN&HB&HX&HC&HO).
    destruct (IH body (name::names) HB) as (target&HT&HR).
    destruct (sf_relation_total M SFEx target (zeroM M)) as (result&HResult).
    destruct (native_named_evaluation_bounded M env a body HB) as (k&HK).
    exists result. split;[exists name,target;auto|].
    exact (named_scope_quantifier_transport M names name body closed original target result ab ac SFEx k
      (or_intror eq_refl) HK HX HC HO HR HResult).
Qed.

Theorem scoped_native_evaluation_functional M env t :forall names a b,
  scoped_native_evaluation M env names t a ->scoped_native_evaluation M env names t b ->a=b.
Proof.
  induction t as [i|eq x y|x IHX y IHY|x IHX y IHY|x a IH|x a IH];
    intros names a0 b0 HLeft HRight;cbn [scoped_native_evaluation] in HLeft,HRight.
  - destruct HLeft as (f&HF&HR),HRight as (g&HG&HS).
    pose proof (raw_source_image_functional M (env i) f g HF HG) as E. subst g.
    exact (named_scope_renaming_functional M names f a0 b0 HR HS).
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

Theorem native_named_scope_empty_exact M env t f :
  native_named_evaluation M env t f ->scoped_native_evaluation M env [] t f.
Proof.
  intro HF. destruct (native_named_scope_evaluation M env t f [] HF) as (g&HG&HR).
  destruct (native_named_evaluation_bounded M env t f HF) as (k&HK).
  pose proof (named_scope_renaming_empty M f g k HK HR) as E. now subst g.
Qed.

Print Assumptions native_named_scope_evaluation.
Print Assumptions native_named_scope_empty_exact.
