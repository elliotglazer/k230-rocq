(** Curry a fixed finite source proof macro by actual II rules. The list
    describes the macro; all formula codes and ambient contexts may be internal. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 NumericalContexts NumericalEnvironments NumericalSourceFull SourceProofWeakening SourceContextProofHelpers SourceLeastOrdinalWitness SourceDerivedRules.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Fixpoint source_finite_telescope M(A:list(carrier M))target out:Prop:=match A with
 |nil=>out=target
 |a::A=>exists inner,source_finite_telescope M A target inner /\sf_relation M SFImpl a inner out end.
Theorem source_finite_telescope_bounded M A target out k:
 (forall a,In a A ->source_bounded M a k) ->source_bounded M target k ->source_finite_telescope M A target out ->source_bounded M out k.
Proof.
 revert out. induction A as[|a A IH];intros out BA BT H;[exact(eq_ind_r(fun out=>source_bounded M out k)BT H)|].
 destruct H as(inner&HInner&HO). exact(proj2(source_bounded_accept_binary M SFImpl a inner out k(or_intror(or_intror eq_refl))HO)
  (conj(BA a(or_introl eq_refl))(IH inner(fun x H=>BA x(or_intror H))BT HInner))).
Qed.
Theorem source_full_finite_telescope M A target out k:
 (forall a,In a A ->source_bounded M a k) ->source_bounded M target k ->source_finite_telescope M A target out ->
 forall cb cc cn,context_bounded M cb cc cn k ->
 (forall b c n,context_bounded M b c n k ->context_included M cb cc cn b c n ->
   (forall a,In a A ->source_full_prv M b c n a) ->source_full_prv M b c n target) ->
 source_full_prv M cb cc cn out.
Proof.
 revert out. induction A as[|a A IH];intros out BA BT H cb cc cn BC Rule.
 - change(out=target)in H. subst out. apply(Rule cb cc cn BC);[intros f HF;exact HF|intros f H;contradiction].
 - destruct H as(inner&HInner&HO).
   pose proof(source_finite_telescope_bounded M A target inner k(fun x H=>BA x(or_intror H))BT HInner)as BI.
   pose proof(proj2(source_bounded_accept_binary M SFImpl a inner out k(or_intror(or_intror eq_refl))HO)(conj(BA a(or_introl eq_refl))BI))as BO.
   destruct(environment_cons_total M cb cc cn a)as(b1&c1&n1&H1).
   pose proof(proj2(context_bounded_cons M cb cc cn a b1 c1 n1 k H1)(conj(BA a(or_introl eq_refl))BC))as B1.
   apply(full_source_II M cb cc cn a inner out b1 c1 n1(ex_intro _ k(conj BO BC)));[|exact H1|exact HO].
   apply(IH inner(fun x H=>BA x(or_intror H))BT HInner b1 c1 n1 B1).
   intros b c n BNew Included Premises.
   apply(Rule b c n BNew).
   + intros f HF. apply Included. exact(source_cons_tail_inclusion M cb cc cn a b1 c1 n1 H1 f HF).
   + intros f[EF|HF];[subst f|exact(Premises f HF)].
     exact(source_full_prv_weaken_bounded M b1 c1 n1 b c n a k
      (source_full_cons_head M cb cc cn a b1 c1 n1 k H1(BA a(or_introl eq_refl))B1)Included BNew).
Qed.
Print Assumptions source_full_finite_telescope.

Theorem source_finite_telescope_total M A target:exists out,source_finite_telescope M A target out.
Proof.
 induction A as[|a A IH].
 - exists target. reflexivity.
 - destruct IH as(inner&HI). destruct(sf_relation_total M SFImpl a inner)as(out&HO). exists out,inner. auto.
Qed.
Theorem source_full_finite_telescope_apply M A target out:
 source_finite_telescope M A target out ->forall b c n,source_full_prv M b c n out ->
 (forall a,In a A ->source_full_prv M b c n a) ->source_full_prv M b c n target.
Proof.
 revert out. induction A as[|a A IH];intros out H b c n POut Premises.
 - change(out=target)in H. now subst out.
 - destruct H as(inner&HInner&HO).
   apply(IH inner HInner b c n).
   + exact(source_full_modus_ponens M b c n a inner out HO POut(Premises a(or_introl eq_refl))).
   + intros f HF. exact(Premises f(or_intror HF)).
Qed.
Print Assumptions source_finite_telescope_bounded.
Print Assumptions source_finite_telescope_total.
Print Assumptions source_full_finite_telescope_apply.
