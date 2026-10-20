(** Fixed propositional proof programs with arbitrary internal source-code
    holes. The kernel compiles each program into the actual source calculus. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SetCodeDescent SourceBounded SchemaConstructorBounds NumericalContexts
  NumericalEnvironments NumericalSourceFull SourceProofWeakening SourceSequents.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Inductive source_prop_template :=
| SPTSlot : nat -> source_prop_template
| SPTFalse : source_prop_template
| SPTImpl : source_prop_template -> source_prop_template -> source_prop_template
| SPTAnd : source_prop_template -> source_prop_template -> source_prop_template
| SPTOr : source_prop_template -> source_prop_template -> source_prop_template.
Fixpoint source_prop_expression (a:source_prop_template) : code_expr :=
  match a with
  | SPTSlot i=>CEvar i | SPTFalse=>CEconst 0
  | SPTImpl a b=>E_sf SFImpl (source_prop_expression a) (source_prop_expression b)
  | SPTAnd a b=>E_sf SFAnd (source_prop_expression a) (source_prop_expression b)
  | SPTOr a b=>E_sf SFOr (source_prop_expression a) (source_prop_expression b)
  end.
Inductive source_prop_program : list source_prop_template -> source_prop_template -> Prop :=
| SPTCtx A a : In a A -> source_prop_program A a
| SPTII A a b : source_prop_program (a::A) b -> source_prop_program A (SPTImpl a b)
| SPTIE A a b : source_prop_program A (SPTImpl a b) -> source_prop_program A a -> source_prop_program A b
| SPTExp A a : source_prop_program A SPTFalse -> source_prop_program A a
| SPTCI A a b : source_prop_program A a -> source_prop_program A b -> source_prop_program A (SPTAnd a b)
| SPTCE1 A a b : source_prop_program A (SPTAnd a b) -> source_prop_program A a
| SPTCE2 A a b : source_prop_program A (SPTAnd a b) -> source_prop_program A b
| SPTDI1 A a b : source_prop_program A a -> source_prop_program A (SPTOr a b)
| SPTDI2 A a b : source_prop_program A b -> source_prop_program A (SPTOr a b)
| SPTDE A a b f : source_prop_program A (SPTOr a b) ->
    source_prop_program (a::A) f -> source_prop_program (b::A) f -> source_prop_program A f
| SPTPc A a b : source_prop_program A (SPTImpl (SPTImpl (SPTImpl a b) a) a).

Definition source_prop_hypotheses M rho A b c n := forall a,
  In a A -> forall f,code_relation M rho (source_prop_expression a) f -> source_full_prv M b c n f.

Lemma source_prop_template_bound M rho a k :
  (forall i,source_bounded M (rho i) k) ->
  schema_expression_bound M rho (source_prop_expression a) k.
Proof.
  intro HB. induction a;cbn [source_prop_expression].
  - apply schema_expression_variable,HB.
  - intros f HF. change (f=zeroM M) in HF. subst f. apply source_bounded_accept_falsity.
  - apply schema_expression_binary;[right;right;reflexivity|exact IHa1|exact IHa2].
  - apply schema_expression_binary;[left;reflexivity|exact IHa1|exact IHa2].
  - apply schema_expression_binary;[right;left;reflexivity|exact IHa1|exact IHa2].
Qed.

Lemma source_prop_template_binary M rho h A B f :
  code_relation M rho (E_sf h (source_prop_expression A) (source_prop_expression B)) f ->
  exists a b,code_relation M rho (source_prop_expression A) a /\
    code_relation M rho (source_prop_expression B) b /\ sf_relation M h a b f.
Proof.
  intro HF. destruct (code_relation_total M (source_prop_expression A) rho) as [a HA].
  destruct (code_relation_total M (source_prop_expression B) rho) as [b HB].
  exists a,b. split;[exact HA|]. split;[exact HB|].
  exact (proj1 (schema_expression_graph M rho h _ _ a b f HA HB) HF).
Qed.

Lemma source_prop_template_join M rho h A B a b f :
  code_relation M rho (source_prop_expression A) a ->
  code_relation M rho (source_prop_expression B) b -> sf_relation M h a b f ->
  code_relation M rho (E_sf h (source_prop_expression A) (source_prop_expression B)) f.
Proof. intros HA HB HF. exact (proj2 (schema_expression_graph M rho h _ _ a b f HA HB) HF). Qed.

Lemma source_prop_hypotheses_cons M rho A b c n a head u v l k :
  (forall i,source_bounded M (rho i) k) -> context_bounded M b c n k ->
  source_prop_hypotheses M rho A b c n ->
  code_relation M rho (source_prop_expression a) head ->
  environment_cons M b c n head u v l -> source_prop_hypotheses M rho (a::A) u v l.
Proof.
  intros HB HC HH HA HCons p HP f HF.
  assert (HNew:context_bounded M u v l k).
  { apply (proj2 (context_bounded_cons M b c n head u v l k HCons)). split.
    - exact (source_prop_template_bound M rho a k HB head HA).
    - exact HC. }
  destruct HP as [<-|HP].
  - pose proof (code_relation_functional M (source_prop_expression a) rho f head HF HA) as E. subst f.
    apply full_source_Ctx.
    + exists k. split;[exact (source_prop_template_bound M rho a k HB head HA)|exact HNew].
    + apply (proj2 (context_member_cons M b c n head u v l head HCons)). now left.
  - apply (source_full_prv_weaken_bounded M b c n u v l f k (HH p HP f HF));[|exact HNew].
    intros h HMember. apply (proj2 (context_member_cons M b c n head u v l h HCons)). now right.
Qed.

Theorem source_prop_program_sound M A a : source_prop_program A a ->
  forall rho k b c n f,(forall i,source_bounded M (rho i) k) ->
    context_bounded M b c n k -> source_prop_hypotheses M rho A b c n ->
    code_relation M rho (source_prop_expression a) f -> source_full_prv M b c n f.
Proof.
  intro HP. induction HP as
    [A a H|A a b HP IHHP|A a b HP1 IHHP1 HP2 IHHP2|A a HP IHHP|
     A a b HP1 IHHP1 HP2 IHHP2|A a b HP IHHP|A a b HP IHHP|
     A a b HP IHHP|A a b HP IHHP|A a b goal HP1 IHHP1 HP2 IHHP2 HP3 IHHP3|A a b];
    intros rho k cb cc cn f HB HC HH HF.
  - exact (HH a H f HF).
  - destruct (source_prop_template_binary M rho SFImpl a b f HF) as [x [y [HX [HY HS]]]].
    destruct (environment_cons_total M cb cc cn x) as [u [v [l HCons]]].
    apply (full_source_II M cb cc cn x y f u v l);[| |exact HCons|exact HS].
    + exists k. split;[exact (source_prop_template_bound M rho (SPTImpl a b) k HB f HF)|exact HC].
    + apply (IHHP rho k u v l y HB).
      * apply (proj2 (context_bounded_cons M cb cc cn x u v l k HCons)).
        split;[exact (source_prop_template_bound M rho a k HB x HX)|exact HC].
      * exact (source_prop_hypotheses_cons M rho A cb cc cn a x u v l k HB HC HH HX HCons).
      * exact HY.
  - destruct (code_relation_total M (source_prop_expression a) rho) as [x HX].
    destruct (sf_relation_total M SFImpl x f) as [imp HI].
    apply (full_source_IE M cb cc cn x f imp).
    + exists k. split;[exact (source_prop_template_bound M rho b k HB f HF)|exact HC].
    + apply (IHHP1 rho k cb cc cn imp HB HC HH).
      exact (source_prop_template_join M rho SFImpl a b x f imp HX HF HI).
    + exact (IHHP2 rho k cb cc cn x HB HC HH HX).
    + exact HI.
  - apply full_source_Exp.
    + exists k. split;[exact (source_prop_template_bound M rho a k HB f HF)|exact HC].
    + exact (IHHP rho k cb cc cn (zeroM M) HB HC HH eq_refl).
  - destruct (source_prop_template_binary M rho SFAnd a b f HF) as [x [y [HX [HY HS]]]].
    apply (full_source_CI M cb cc cn x y f).
    + exists k. split;[exact (source_prop_template_bound M rho (SPTAnd a b) k HB f HF)|exact HC].
    + exact (IHHP1 rho k cb cc cn x HB HC HH HX).
    + exact (IHHP2 rho k cb cc cn y HB HC HH HY).
    + exact HS.
  - destruct (code_relation_total M (source_prop_expression b) rho) as [y HY].
    destruct (sf_relation_total M SFAnd f y) as [conj HS].
    apply (full_source_CE1 M cb cc cn f y conj).
    + exists k. split;[exact (source_prop_template_bound M rho a k HB f HF)|exact HC].
    + apply (IHHP rho k cb cc cn conj HB HC HH).
      exact (source_prop_template_join M rho SFAnd a b f y conj HF HY HS).
    + exact HS.
  - destruct (code_relation_total M (source_prop_expression a) rho) as [x HX].
    destruct (sf_relation_total M SFAnd x f) as [conj HS].
    apply (full_source_CE2 M cb cc cn x f conj).
    + exists k. split;[exact (source_prop_template_bound M rho b k HB f HF)|exact HC].
    + apply (IHHP rho k cb cc cn conj HB HC HH).
      exact (source_prop_template_join M rho SFAnd a b x f conj HX HF HS).
    + exact HS.
  - destruct (source_prop_template_binary M rho SFOr a b f HF) as [x [y [HX [HY HS]]]].
    apply (full_source_DI1 M cb cc cn x y f).
    + exists k. split;[exact (source_prop_template_bound M rho (SPTOr a b) k HB f HF)|exact HC].
    + exact (IHHP rho k cb cc cn x HB HC HH HX).
    + exact HS.
  - destruct (source_prop_template_binary M rho SFOr a b f HF) as [x [y [HX [HY HS]]]].
    apply (full_source_DI2 M cb cc cn x y f).
    + exists k. split;[exact (source_prop_template_bound M rho (SPTOr a b) k HB f HF)|exact HC].
    + exact (IHHP rho k cb cc cn y HB HC HH HY).
    + exact HS.
  - destruct (code_relation_total M (source_prop_expression a) rho) as [x HX].
    destruct (code_relation_total M (source_prop_expression b) rho) as [y HY].
    destruct (sf_relation_total M SFOr x y) as [disj HS].
    destruct (environment_cons_total M cb cc cn x) as [u [v [l HConsX]]].
    destruct (environment_cons_total M cb cc cn y) as [u' [v' [l' HConsY]]].
    apply (full_source_DE_three M cb cc cn x y f disj u v l u' v' l').
    + exists k. split;[exact (source_prop_template_bound M rho goal k HB f HF)|exact HC].
    + exists k. repeat split;try exact HC.
      * exact (source_prop_template_bound M rho a k HB x HX).
      * exact (source_prop_template_bound M rho b k HB y HY).
      * exact (source_prop_template_bound M rho goal k HB f HF).
    + apply (IHHP1 rho k cb cc cn disj HB HC HH).
      exact (source_prop_template_join M rho SFOr a b x y disj HX HY HS).
    + apply (IHHP2 rho k u v l f HB).
      * apply (proj2 (context_bounded_cons M cb cc cn x u v l k HConsX)).
        split;[exact (source_prop_template_bound M rho a k HB x HX)|exact HC].
      * exact (source_prop_hypotheses_cons M rho A cb cc cn a x u v l k HB HC HH HX HConsX).
      * exact HF.
    + apply (IHHP3 rho k u' v' l' f HB).
      * apply (proj2 (context_bounded_cons M cb cc cn y u' v' l' k HConsY)).
        split;[exact (source_prop_template_bound M rho b k HB y HY)|exact HC].
      * exact (source_prop_hypotheses_cons M rho A cb cc cn b y u' v' l' k HB HC HH HY HConsY).
      * exact HF.
    + exact HConsX.
    + exact HConsY.
    + exact HS.
  - destruct (source_prop_template_binary M rho SFImpl (SPTImpl (SPTImpl a b) a) a f HF)
      as [y [x [HY [HX HFinal]]]].
    destruct (source_prop_template_binary M rho SFImpl (SPTImpl a b) a y HY)
      as [imp [x' [HI [HX' HMid]]]].
    pose proof (code_relation_functional M (source_prop_expression a) rho x' x HX' HX) as E. subst x'.
    destruct (source_prop_template_binary M rho SFImpl a b imp HI) as [x' [z [HX2 [HZ HFirst]]]].
    pose proof (code_relation_functional M (source_prop_expression a) rho x' x HX2 HX) as E. subst x'.
    apply (full_source_Pc M cb cc cn x z imp y f).
    + exists k. split.
      * exact (source_prop_template_bound M rho (SPTImpl (SPTImpl (SPTImpl a b) a) a) k HB f HF).
      * exact HC.
    + exact HFirst.
    + exact HMid.
    + exact HFinal.
Qed.

Print Assumptions source_prop_template_bound.
Print Assumptions source_prop_program_sound.
