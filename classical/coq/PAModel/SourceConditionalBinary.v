(** Conditional propositional congruence for nonstandard source holes. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SetCodeDescent SourceBounded
 SourceZFRProvability SourceConditionalProofs SourceWitnessProofComposition SourcePropositionalTemplates SourcePropositionalRebase.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition source_binary_prop h A B :=match h with
 | SFAnd=>SPTAnd A B | SFOr=>SPTOr A B | _=>SPTImpl A B end.
Definition source_covariance_first h A C :=match h with SFImpl=>SPTImpl C A|_=>SPTImpl A C end.
Lemma source_conditional_binary_program h C A B D E:
 sf_binary h ->source_prop_program
 [SPTImpl C(source_covariance_first h A D);SPTImpl C(SPTImpl B E)]
 (SPTImpl C(SPTImpl(source_binary_prop h A B)(source_binary_prop h D E))).
Proof.
 intros[HH|[HH|HH]];subst h;cbn[source_covariance_first source_binary_prop].
 - apply SPTII,SPTII,SPTCI.
   + apply(SPTIE _ A D).
     * apply(SPTIE _ C(SPTImpl A D));apply SPTCtx;cbn;tauto.
     * apply(SPTCE1 _ A B),SPTCtx;cbn;tauto.
   + apply(SPTIE _ B E).
     * apply(SPTIE _ C(SPTImpl B E));apply SPTCtx;cbn;tauto.
     * apply(SPTCE2 _ A B),SPTCtx;cbn;tauto.
 - apply SPTII,SPTII. apply(SPTDE _ A B).
   + apply SPTCtx;cbn;tauto.
   + apply SPTDI1. apply(SPTIE _ A D).
     * apply(SPTIE _ C(SPTImpl A D));apply SPTCtx;cbn;tauto.
     * apply SPTCtx;cbn;tauto.
   + apply SPTDI2. apply(SPTIE _ B E).
     * apply(SPTIE _ C(SPTImpl B E));apply SPTCtx;cbn;tauto.
     * apply SPTCtx;cbn;tauto.
 - apply SPTII,SPTII,SPTII. apply(SPTIE _ B E).
   + apply(SPTIE _ C(SPTImpl B E));apply SPTCtx;cbn;tauto.
   + apply(SPTIE _ A B);[apply SPTCtx;cbn;tauto|].
     apply(SPTIE _ D A).
     * apply(SPTIE _ C(SPTImpl D A));apply SPTCtx;cbn;tauto.
     * apply SPTCtx;cbn;tauto.
Qed.

Definition source_conditional_five M (C A B D E:carrier M) i:=match i with
 |0=>C|1=>A|2=>B|3=>D|_=>E end.
Lemma source_binary_prop_graph M rho h A B a b out:
 sf_binary h ->code_relation M rho(source_prop_expression A)a ->
 code_relation M rho(source_prop_expression B)b ->sf_relation M h a b out ->
 code_relation M rho(source_prop_expression(source_binary_prop h A B))out.
Proof.
 intros[HH|[HH|HH]]HA HB HO;subst h;
  exact(source_prop_template_join M rho _ A B a b out HA HB HO).
Qed.

Theorem source_conditional_implies_binary M h condition a b d e left right k:
 sf_binary h ->source_bounded M condition k ->source_bounded M a k ->source_bounded M b k ->
 source_bounded M d k ->source_bounded M e k ->
 source_conditional_equivalent M condition a d ->source_conditional_implies M condition b e ->
 sf_relation M h a b left ->sf_relation M h d e right ->source_conditional_implies M condition left right.
Proof.
 intros HH BC BA BB BD BE[HAD HDA]HBE HL HR map HM law HLaw.
 set(rho:=source_conditional_five M condition a b d e).
 destruct(sf_relation_total M SFImpl b e)as(p2&HP2).
 destruct(sf_relation_total M SFImpl condition p2)as(first2&HFirst2).
 pose proof(HBE p2 HP2 first2 HFirst2)as P2.
 assert(Bounds:forall i,source_bounded M(rho i)k).
 { intros[|[|[|[|i]]]];cbn[rho source_conditional_five];assumption. }
 assert(R2:code_relation M rho(source_prop_expression(SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 2)(SPTSlot 4))))first2).
 { exact(source_prop_template_join M rho SFImpl(SPTSlot 0)(SPTImpl(SPTSlot 2)(SPTSlot 4)) condition p2 first2 eq_refl
   (source_prop_template_join M rho SFImpl(SPTSlot 2)(SPTSlot 4)b e p2 eq_refl eq_refl HP2)HFirst2). }
 assert(RLaw:code_relation M rho(source_prop_expression(SPTImpl(SPTSlot 0)
   (SPTImpl(source_binary_prop h(SPTSlot 1)(SPTSlot 2))(source_binary_prop h(SPTSlot 3)(SPTSlot 4)))))law).
 { apply(source_prop_template_join M rho SFImpl(SPTSlot 0) _ condition map law eq_refl);[|exact HLaw].
   apply(source_prop_template_join M rho SFImpl _ _ left right map);[| |exact HM].
   - exact(source_binary_prop_graph M rho h(SPTSlot 1)(SPTSlot 2)a b left HH eq_refl eq_refl HL).
   - exact(source_binary_prop_graph M rho h(SPTSlot 3)(SPTSlot 4)d e right HH eq_refl eq_refl HR). }
 destruct(sf_relation_total M SFImpl
  (match h with SFImpl=>d|_=>a end)(match h with SFImpl=>a|_=>d end))as(p1&HP1).
 destruct(sf_relation_total M SFImpl condition p1)as(first1&HFirst1).
 assert(P1:source_zfr_provable M first1).
 { destruct HH as[HH|[HH|HH]];subst h;[exact(HAD p1 HP1 first1 HFirst1)|exact(HAD p1 HP1 first1 HFirst1)|exact(HDA p1 HP1 first1 HFirst1)]. }
 assert(R1:code_relation M rho(source_prop_expression(SPTImpl(SPTSlot 0)(source_covariance_first h(SPTSlot 1)(SPTSlot 3))))first1).
 { apply(source_prop_template_join M rho SFImpl(SPTSlot 0) _ condition p1 first1 eq_refl);[|exact HFirst1].
   destruct HH as[HH|[HH|HH]];subst h;cbn[source_covariance_first].
   - exact(source_prop_template_join M rho SFImpl(SPTSlot 1)(SPTSlot 3)a d p1 eq_refl eq_refl HP1).
   - exact(source_prop_template_join M rho SFImpl(SPTSlot 1)(SPTSlot 3)a d p1 eq_refl eq_refl HP1).
   - exact(source_prop_template_join M rho SFImpl(SPTSlot 3)(SPTSlot 1)d a p1 eq_refl eq_refl HP1). }
 exact(source_zfr_prop_two M _ _ _ (source_conditional_binary_program h(SPTSlot 0)(SPTSlot 1)(SPTSlot 2)(SPTSlot 3)(SPTSlot 4)HH)
  rho k first1 first2 law Bounds R1 R2 RLaw P1 P2).
Qed.

Print Assumptions source_conditional_implies_binary.
