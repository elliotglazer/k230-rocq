(** Renaming and bound inversion for a finite propositional skeleton with
    arbitrary internally coded source formulas in its slots. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 SourcePropositionalTemplates NumericalRenaming.
Unset Implicit Arguments.
Fixpoint source_prop_slots(P:nat->Prop)a:Prop:=match a with
 |SPTSlot i=>P i|SPTFalse=>True
 |SPTImpl a b|SPTAnd a b|SPTOr a b=>source_prop_slots P a /\source_prop_slots P b end.

Theorem source_prop_renaming M rho sigma b c n delta a f g :
 source_prop_slots(fun i=>numerical_renaming M(rho i)b c n delta(sigma i))a ->
 code_relation M rho(source_prop_expression a)f ->code_relation M sigma(source_prop_expression a)g ->
 numerical_renaming M f b c n delta g.
Proof.
 revert f g. induction a;intros f g HA HF HG;cbn[source_prop_slots]in HA.
 - change(f=rho n0)in HF. change(g=sigma n0)in HG. now subst f g.
 - change(f=zeroM M)in HF. change(g=zeroM M)in HG. subst f g.
   exact(proj2(numerical_renaming_invalid M(zeroM M)b c n delta(zeroM M)(or_introl eq_refl))eq_refl).
 - destruct(source_prop_template_binary M rho SFImpl a1 a2 f HF)as(u&v&HU&HV&HSource).
   destruct(source_prop_template_binary M sigma SFImpl a1 a2 g HG)as(s&t&HS&HT&HTarget).
   apply(proj2(numerical_renaming_binary M SFImpl u v f b c n delta g(or_intror(or_intror eq_refl))HSource)).
   exists s,t. exact(conj(IHa1 u s(proj1 HA)HU HS)(conj(IHa2 v t(proj2 HA)HV HT)HTarget)).
 - destruct(source_prop_template_binary M rho SFAnd a1 a2 f HF)as(u&v&HU&HV&HSource).
   destruct(source_prop_template_binary M sigma SFAnd a1 a2 g HG)as(s&t&HS&HT&HTarget).
   apply(proj2(numerical_renaming_binary M SFAnd u v f b c n delta g(or_introl eq_refl)HSource)).
   exists s,t. exact(conj(IHa1 u s(proj1 HA)HU HS)(conj(IHa2 v t(proj2 HA)HV HT)HTarget)).
 - destruct(source_prop_template_binary M rho SFOr a1 a2 f HF)as(u&v&HU&HV&HSource).
   destruct(source_prop_template_binary M sigma SFOr a1 a2 g HG)as(s&t&HS&HT&HTarget).
   apply(proj2(numerical_renaming_binary M SFOr u v f b c n delta g(or_intror(or_introl eq_refl))HSource)).
   exists s,t. exact(conj(IHa1 u s(proj1 HA)HU HS)(conj(IHa2 v t(proj2 HA)HV HT)HTarget)).
Qed.

Theorem source_prop_bound_inversion M rho a f k :code_relation M rho(source_prop_expression a)f ->
 source_bounded M f k ->source_prop_slots(fun i=>source_bounded M(rho i)k)a.
Proof.
 revert f. induction a;intros f HF HB;cbn[source_prop_slots].
 - change(f=rho n)in HF. now subst f.
 - exact I.
 - destruct(source_prop_template_binary M rho SFImpl a1 a2 f HF)as(u&v&HU&HV&HR).
   destruct(proj1(source_bounded_accept_binary M SFImpl u v f k(or_intror(or_intror eq_refl))HR)HB)as[BU BV].
   exact(conj(IHa1 u HU BU)(IHa2 v HV BV)).
 - destruct(source_prop_template_binary M rho SFAnd a1 a2 f HF)as(u&v&HU&HV&HR).
   destruct(proj1(source_bounded_accept_binary M SFAnd u v f k(or_introl eq_refl)HR)HB)as[BU BV].
   exact(conj(IHa1 u HU BU)(IHa2 v HV BV)).
 - destruct(source_prop_template_binary M rho SFOr a1 a2 f HF)as(u&v&HU&HV&HR).
   destruct(proj1(source_bounded_accept_binary M SFOr u v f k(or_intror(or_introl eq_refl))HR)HB)as[BU BV].
   exact(conj(IHa1 u HU BU)(IHa2 v HV BV)).
Qed.
Print Assumptions source_prop_renaming.
Print Assumptions source_prop_bound_inversion.
