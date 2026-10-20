(** Finite propositional programs combined with actual named existential
    rules. Arbitrary internal formula holes are retained unchanged. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 SourcePropositionalTemplates SourceDescriptorProvability SourceDescriptorPrograms
 SourceDescriptorNamedExists SourceNamedVacuity SourceNamedElimination SourceNamedQuantifierRules.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Fixpoint source_prop_named_vacuity M rho x a :Prop :=match a with
 |SPTSlot i=>source_named_vacuous M x(rho i)|SPTFalse=>True
 |SPTImpl a b|SPTAnd a b|SPTOr a b=>
   source_prop_named_vacuity M rho x a /\source_prop_named_vacuity M rho x b end.

Theorem source_prop_named_vacuity_sound M rho x a f :
 source_prop_named_vacuity M rho x a ->code_relation M rho(source_prop_expression a) f ->
 source_named_vacuous M x f.
Proof.
 revert f. induction a;intros f HV HF;cbn[source_prop_named_vacuity]in HV.
 - change(f=rho n)in HF. now subst f.
 - change(f=zeroM M)in HF. subst f.
   exact(source_named_vacuous_above_bound M(zeroM M)x(zeroM M)
     (source_bounded_accept_falsity M(zeroM M))(coding_zero_lt_succ M x)).
 - destruct(source_prop_template_binary M rho SFImpl a1 a2 f HF)as(u&v&HU&HW&HR).
   exact(source_named_vacuous_binary M SFImpl u v f x(or_intror(or_intror eq_refl)) HR
    (IHa1 u(proj1 HV) HU)(IHa2 v(proj2 HV) HW)).
 - destruct(source_prop_template_binary M rho SFAnd a1 a2 f HF)as(u&v&HU&HW&HR).
   exact(source_named_vacuous_binary M SFAnd u v f x(or_introl eq_refl) HR
    (IHa1 u(proj1 HV) HU)(IHa2 v(proj2 HV) HW)).
 - destruct(source_prop_template_binary M rho SFOr a1 a2 f HF)as(u&v&HU&HW&HR).
   exact(source_named_vacuous_binary M SFOr u v f x(or_intror(or_introl eq_refl)) HR
    (IHa1 u(proj1 HV) HU)(IHa2 v(proj2 HV) HW)).
Qed.

Definition source_descriptor_template M T rho a :=forall f,
 code_relation M rho(source_prop_expression a) f ->source_descriptor_provable M T f.

Theorem source_descriptor_template_program M T rho k A a :
 (forall i,source_bounded M(rho i) k) ->source_prop_program A a ->
 (forall p,In p A ->source_descriptor_template M T rho p) ->source_descriptor_template M T rho a.
Proof. intros HB HP HH f HF. exact(source_descriptor_prop_program M T A a HP rho k f HB HH HF). Qed.

Theorem source_descriptor_template_named_exists M T rho x a index goal body :
 code_relation M rho(source_prop_expression a)body ->
 source_named_quantifier M false x body(rho index) ->source_prop_named_vacuity M rho x goal ->
 source_descriptor_template M T rho(SPTImpl a goal) ->
 source_descriptor_template M T rho(SPTImpl(SPTSlot index)goal).
Proof.
 intros HA HQ HV HP f HF.
 destruct(source_prop_template_binary M rho SFImpl(SPTSlot index)goal f HF)as(exf&g&HEx&HG&HR).
 change(exf=rho index)in HEx. subst exf.
 destruct(sf_relation_total M SFImpl body g)as(point&HPoint).
 exact(source_descriptor_named_exists_implication M T x body(rho index)g point f HQ
  (source_prop_named_vacuity_sound M rho x goal g HV HG) HPoint HR
  (HP point(source_prop_template_join M rho SFImpl a goal body g point HA HG HPoint))).
Qed.

Theorem source_descriptor_template_named_intro M T rho x a index body k :
 source_bounded M body k ->code_relation M rho(source_prop_expression a)body ->
 source_named_quantifier M false x body(rho index) ->
 source_descriptor_template M T rho(SPTImpl a(SPTSlot index)).
Proof.
 intros HB HA HQ f HF.
 destruct(source_prop_template_binary M rho SFImpl a(SPTSlot index)f HF)as(u&exf&HU&HEx&HR).
 change(exf=rho index)in HEx. subst exf.
 rewrite(code_relation_functional M _ rho u body HU HA)in HR.
 exact(source_descriptor_named_exists_introduction_law M T x body(rho index)f k HB HQ HR).
Qed.

Print Assumptions source_prop_named_vacuity_sound.
Print Assumptions source_descriptor_template_program.
Print Assumptions source_descriptor_template_named_exists.
Print Assumptions source_descriptor_template_named_intro.
