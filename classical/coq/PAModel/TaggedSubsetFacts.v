(** The empty marker and a selected singleton provide the subset premises
    of tagged eligibility. These are numerical proof programs. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  ProofTemplates NumericalEquality NamedLeibnizSteps NamedBinderFresh
  TemplateBinderFresh TemplateNamedSubstitution StoppingInstantiation
  NumericalKP0 NumericalKP0Requests NumericalKP0Eligibility NumericalSingleton NumericalTaggedComprehension
  TemplateFormulaFresh NumericalVacuitySteps TemplatePropositional ProofMacros
  QuantifierMacros NumericalBootstrap QuotientAtomTemplates ContextualPropositional.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Theorem numerical_empty_subset M rho T B K Z tv kv zv :
  code_relation M rho T tv -> code_relation M rho K kv -> code_relation M rho Z zv ->
  zv<>zeroM M -> kv<>zeroM M -> zv<>kv -> tv<>zv -> tv<>kv ->
  ns_proof M rho (E_wim (E_wal Z (E_wn (E_wel Z T))) (E_ksubset T B K)).
Proof.
  intros HT HK HZ HZ0 HK0 HZK HTZ HTK.
  set (Empty:=E_wal Z (E_wn (E_wel Z T))).
  set (F:=E_wn (E_wel Z T)). set (V:=E_wn (E_wel K T)).
  assert (RZ:expression_named_replace M rho rho zv kv Z K).
  { intros a b HA HB. rewrite (code_relation_functional M Z rho a zv HA HZ),
      (code_relation_functional M K rho b kv HB HK). now left. }
  assert (RT:expression_named_replace M rho rho zv kv T T).
  { intros a b HA HB. rewrite (code_relation_functional M T rho a tv HA HT),
      (code_relation_functional M T rho b tv HB HT). now right. }
  assert (Sub:expression_named_substitution M rho rho zv kv F V).
  { apply expression_ns_negation;[exact HZ0|].
    apply (expression_ns_atom M rho rho zv kv false);assumption. }
  assert (BA:expression_binder_absent M rho kv F).
  { apply expression_binder_absent_negation,expression_binder_absent_atom;now left. }
  destruct (code_relation_total M F rho) as [f HF].
  destruct (code_relation_total M V rho) as [v HV].
  pose proof (proj1 (ns_stopping_instantiation M rho Z K F V zv kv f v
    HZ HK HF HV HZK (BA f HF) (Sub f v HF HV))) as HS.
  assert (HP:ns_proof M rho (E_wim Empty (E_wim (E_wel K T) (E_wel K B)))).
  { apply (ns_proof_macro M rho (E_wim Empty V :: nil)).
    - intros e [<-|[]]. exact HS.
    - eapply macro_syl;[apply PM_input;now left|].
      apply PM_template,template_negative_implication. }
  apply (ns_proof_macro M rho (E_vac K Empty :: E_wim Empty (E_wim (E_wel K T) (E_wel K B)) :: nil)).
  - intros e [<-|[<-|[]]].
    + apply (kp0_expression_fresh_vacuity M rho K Empty kv HK).
      apply expression_fresh_universal.
      * intros a HA. rewrite (code_relation_functional M Z rho a zv HA HZ). exact HZK.
      * apply expression_fresh_negation;[exact HK0|]. apply expression_fresh_atom;[now left| |].
        -- intros a HA. rewrite (code_relation_functional M Z rho a zv HA HZ). exact HZK.
        -- intros a HA. rewrite (code_relation_functional M T rho a tv HA HT). exact HTK.
    + exact HP.
  - unfold E_ksubset. eapply macro_syl;[apply PM_input;now left|].
    apply macro_all_monotone,PM_input;now right;left.
Qed.

Theorem numerical_singleton_subset M rho X P B K Z xv pv bv kv zv :
  code_relation M rho X xv -> code_relation M rho P pv -> code_relation M rho B bv ->
  code_relation M rho K kv -> code_relation M rho Z zv ->
  kv<>zeroM M -> zv<>kv -> pv<>zv -> xv<>zv -> xv<>kv -> pv<>kv -> bv<>kv ->
  ns_proof M rho (E_wim (E_wa (E_raw_singleton X P Z) (E_wel X B)) (E_ksubset P B K)).
Proof.
  intros HX HP HB HK HZ HK0 HZK HPZ HXZ HXK HPK HBK.
  set (H:=E_wa (E_raw_singleton X P Z) (E_wel X B)).
  assert (Hpoint:ns_proof M rho (E_wim H (E_wim (E_wel K P) (E_wel K B)))).
  { apply (ns_proof_macro M rho
      (E_wim (E_wal Z (E_wim (E_wel Z P) (E_weq Z X)))
        (E_wim (E_wel K P) (E_weq K X)) ::
       E_wim (E_weq K X) (E_weq X K) ::
       E_wim (E_weq X K) (E_wim (E_wel X B) (E_wel K B)) :: nil)).
    - intros e [<-|[<-|[<-|[]]]].
      + exact (singleton_profile_specialization M rho Z K X P zv kv xv pv HZ HK HX HP HZK HPZ HXZ).
      + apply ns_proof_symmetry.
      + apply numerical_tagged_membership_transport.
    - apply macro_discharge. do 2 apply macro_deduction.
      eapply md_mp with (a:=E_wel X B).
      + unfold H. apply tagged_md_right with (a:=E_raw_singleton X P Z),md_hyp;now right;left.
      + eapply md_mp with (a:=E_weq X K).
        * eapply md_mp with (a:=E_weq K X).
          -- eapply md_mp with (a:=E_wel K P);[apply md_hyp;now left|].
             eapply md_mp with (a:=E_wal Z (E_wim (E_wel Z P) (E_weq Z X))).
             ++ apply tagged_md_right with (a:=E_wel X P).
                unfold H. apply tagged_md_left with (b:=E_wel X B),md_hyp;now right;left.
             ++ apply md_global,PM_input;now left.
          -- apply md_global,PM_input;now right;left.
        * apply md_global,PM_input;now right;right;left. }
  apply (ns_proof_macro M rho (E_vac K H :: E_wim H (E_wim (E_wel K P) (E_wel K B)) :: nil)).
  - intros e [<-|[<-|[]]].
    + apply (kp0_expression_fresh_vacuity M rho K H kv HK).
      unfold H,E_raw_singleton. apply expression_fresh_conjunction;[exact HK0| |].
      * apply expression_fresh_conjunction;[exact HK0| |].
        -- apply expression_fresh_atom;[now left| |];intros a HA;
             first [rewrite (code_relation_functional M X rho a xv HA HX);exact HXK
                   |rewrite (code_relation_functional M P rho a pv HA HP);exact HPK].
        -- apply expression_fresh_universal.
           ++ intros a HA. rewrite (code_relation_functional M Z rho a zv HA HZ). exact HZK.
           ++ apply expression_fresh_implication;
                apply expression_fresh_atom;try (now left);try (now right);intros a HA;
                first [rewrite (code_relation_functional M Z rho a zv HA HZ);exact HZK
                      |rewrite (code_relation_functional M P rho a pv HA HP);exact HPK
                      |rewrite (code_relation_functional M X rho a xv HA HX);exact HXK].
      * apply expression_fresh_atom;[now left| |];intros a HA;
          first [rewrite (code_relation_functional M X rho a xv HA HX);exact HXK
                |rewrite (code_relation_functional M B rho a bv HA HB);exact HBK].
    + exact Hpoint.
  - unfold E_ksubset. eapply macro_syl;[apply PM_input;now left|].
    apply macro_all_monotone,PM_input;now right;left.
Qed.

Print Assumptions numerical_empty_subset.
Print Assumptions numerical_singleton_subset.
