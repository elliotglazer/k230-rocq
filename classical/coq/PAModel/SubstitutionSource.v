(** Finite-source calibration to the library's actual de Bruijn subst_form.
    The host syntax is finite; all map parameters may be model elements. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  ProofTemplates SetFormulaCodes ZFCFiniteSourceCodes SetSchemaConstructors
  NumericalSubstitutionMaps NumericalSubstitution StandardModel.
From Undecidability.FOL Require Import Syntax.BinSig Sets.Signatures.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Lemma substitution_source_constructor_graph M rho h A B a b f :
  code_relation M rho A a -> code_relation M rho B b ->
  (code_relation M rho (E_sf h A B) f <-> sf_relation M h a b f).
Proof.
  intros HA HB.
  replace (E_sf h A B) with
    (code_subst (sf_env A B) (E_sf h (CEvar 0) (CEvar 1)))
    by (destruct h; reflexivity).
  unfold sf_relation. apply code_subst_graph.
  intros [|i]; cbn [sf_env]; assumption.
Qed.

Lemma substitution_source_term_index (sigma : nat -> sf_term) (t : sf_term) :
  sf_index (subst_term sigma t) = sf_index (sigma (sf_index t)).
Proof. destruct t as [i|[]]. reflexivity. Qed.

Lemma substitution_source_atom_expression {ff} (P : ZF_Preds)
    (ts : Vector.t sf_term 2) (sigma : nat -> sf_term) :
  sf_expression (subst_form sigma
    (atom P ts : @Core.form sig_empty ZFSignature.ZF_pred_sig full_operators ff)) =
  E_sf (match P with elem => SFMember | equal => SFEqual end)
    (CEconst (sf_index (sigma (sf_index (Vector.hd ts)))))
    (CEconst (sf_index (sigma (sf_index (Vector.hd (Vector.tl ts)))))).
Proof.
  rewrite (Vector.eta ts), (Vector.eta (Vector.tl ts)).
  destruct P; cbn [subst_form sf_expression Vector.map Vector.hd Vector.tl VectorDef.hd VectorDef.tl VectorDef.caseS];
    try rewrite !substitution_source_term_index; reflexivity.
Qed.

Lemma substitution_source_lift_lookup M b c n base d e m sigma :
  substitution_lift M b c n base d e m ->
  (forall i, substitution_lookup M b c n base (code_numeral M i)
    (code_numeral M (sf_index (sigma i)))) ->
  forall i, substitution_lookup M d e m (succM M base) (code_numeral M i)
    (code_numeral M (sf_index (up sigma i))).
Proof.
  intros Hlift Hlookup [|i]; rewrite source_up_substitution_index.
  - exact (proj1 (proj2 Hlift)).
  - cbn [code_numeral]. apply (proj2 (proj2 Hlift)). apply Hlookup.
Qed.

Theorem fixed_source_substitution {ff} M rho
    (phi : @Core.form sig_empty ZFSignature.ZF_pred_sig full_operators ff) :
  forall sigma eb c n base f v,
  (forall i, substitution_lookup M eb c n base (code_numeral M i)
    (code_numeral M (sf_index (sigma i)))) ->
  code_relation M rho (sf_expression phi) f ->
  code_relation M rho (sf_expression (subst_form sigma phi)) v ->
  numerical_substitution M f eb c n base v.
Proof.
  induction phi; intros sigma eb c n base f v Hlookup Hf Hv.
  - change (f=zeroM M) in Hf. change (v=zeroM M) in Hv. subst f v.
    apply (proj2 (numerical_substitution_invalid M (zeroM M) eb c n base (zeroM M)
      (or_introl eq_refl))). reflexivity.
  - rewrite substitution_source_atom_expression in Hv.
    destruct P.
    + apply (proj2 (numerical_substitution_member M
        (code_numeral M (sf_index (Vector.hd t)))
        (code_numeral M (sf_index (Vector.hd (Vector.tl t)))) f eb c n base v
        (proj1 (substitution_source_constructor_graph M rho SFMember
          (CEconst (sf_index (Vector.hd t))) (CEconst (sf_index (Vector.hd (Vector.tl t))))
          _ _ f eq_refl eq_refl) Hf))).
      exists (code_numeral M (sf_index (sigma (sf_index (Vector.hd t))))),
        (code_numeral M (sf_index (sigma (sf_index (Vector.hd (Vector.tl t)))))).
      split; [apply Hlookup|]. split; [apply Hlookup|].
      exact (proj1 (substitution_source_constructor_graph M rho SFMember
        (CEconst (sf_index (sigma (sf_index (Vector.hd t)))))
        (CEconst (sf_index (sigma (sf_index (Vector.hd (Vector.tl t))))))
        _ _ v eq_refl eq_refl) Hv).
    + apply (proj2 (numerical_substitution_equal M
        (code_numeral M (sf_index (Vector.hd t)))
        (code_numeral M (sf_index (Vector.hd (Vector.tl t)))) f eb c n base v
        (proj1 (substitution_source_constructor_graph M rho SFEqual
          (CEconst (sf_index (Vector.hd t))) (CEconst (sf_index (Vector.hd (Vector.tl t))))
          _ _ f eq_refl eq_refl) Hf))).
      exists (code_numeral M (sf_index (sigma (sf_index (Vector.hd t))))),
        (code_numeral M (sf_index (sigma (sf_index (Vector.hd (Vector.tl t)))))).
      split; [apply Hlookup|]. split; [apply Hlookup|].
      exact (proj1 (substitution_source_constructor_graph M rho SFEqual
        (CEconst (sf_index (sigma (sf_index (Vector.hd t)))))
        (CEconst (sf_index (sigma (sf_index (Vector.hd (Vector.tl t))))))
        _ _ v eq_refl eq_refl) Hv).
  - destruct (code_relation_total M (sf_expression phi1) rho) as [a Ha].
    destruct (code_relation_total M (sf_expression phi2) rho) as [d Hd].
    destruct (code_relation_total M (sf_expression (subst_form sigma phi1)) rho) as [x Hx].
    destruct (code_relation_total M (sf_expression (subst_form sigma phi2)) rho) as [y Hy].
    pose proof (IHphi1 sigma eb c n base a x Hlookup Ha Hx) as Ix.
    pose proof (IHphi2 sigma eb c n base d y Hlookup Hd Hy) as Iy.
    destruct b0.
    + apply (proj2 (numerical_substitution_binary M SFAnd a d f eb c n base v
        (or_introl eq_refl)
        (proj1 (substitution_source_constructor_graph M rho SFAnd _ _ a d f Ha Hd) Hf))).
      exists x,y. split; [exact Ix|]. split; [exact Iy|].
      exact (proj1 (substitution_source_constructor_graph M rho SFAnd _ _ x y v Hx Hy) Hv).
    + apply (proj2 (numerical_substitution_binary M SFOr a d f eb c n base v
        (or_intror (or_introl eq_refl))
        (proj1 (substitution_source_constructor_graph M rho SFOr _ _ a d f Ha Hd) Hf))).
      exists x,y. split; [exact Ix|]. split; [exact Iy|].
      exact (proj1 (substitution_source_constructor_graph M rho SFOr _ _ x y v Hx Hy) Hv).
    + apply (proj2 (numerical_substitution_binary M SFImpl a d f eb c n base v
        (or_intror (or_intror eq_refl))
        (proj1 (substitution_source_constructor_graph M rho SFImpl _ _ a d f Ha Hd) Hf))).
      exists x,y. split; [exact Ix|]. split; [exact Iy|].
      exact (proj1 (substitution_source_constructor_graph M rho SFImpl _ _ x y v Hx Hy) Hv).
  - destruct (substitution_lift_total M eb c n base) as [d [e [m Hlift]]].
    destruct (code_relation_total M (sf_expression phi) rho) as [a Ha].
    destruct (code_relation_total M (sf_expression (subst_form (up sigma) phi)) rho) as [w Hw].
    pose proof (IHphi (up sigma) d e m (succM M base) a w
      (substitution_source_lift_lookup M eb c n base d e m sigma Hlift Hlookup) Ha Hw) as IH.
    destruct q.
    + apply (proj2 (numerical_substitution_quantifier M true a f eb c n base v
        (proj1 (substitution_source_constructor_graph M rho SFAll _ (CEconst 0) a
          (zeroM M) f Ha eq_refl) Hf))).
      exists d,e,m,w. split; [exact Hlift|]. split; [exact IH|].
      exact (proj1 (substitution_source_constructor_graph M rho SFAll _ (CEconst 0) w
        (zeroM M) v Hw eq_refl) Hv).
    + apply (proj2 (numerical_substitution_quantifier M false a f eb c n base v
        (proj1 (substitution_source_constructor_graph M rho SFEx _ (CEconst 0) a
          (zeroM M) f Ha eq_refl) Hf))).
      exists d,e,m,w. split; [exact Hlift|]. split; [exact IH|].
      exact (proj1 (substitution_source_constructor_graph M rho SFEx _ (CEconst 0) w
        (zeroM M) v Hw eq_refl) Hv).
Qed.

Theorem standard_source_substitution {ff}
    (phi : @Core.form sig_empty ZFSignature.ZF_pred_sig full_operators ff)
    sigma b c n base :
  (forall i, substitution_lookup natModel b c n base i (sf_index (sigma i))) ->
  numerical_substitution natModel (sf_encode phi) b c n base
    (sf_encode (subst_form sigma phi)).
Proof.
  intro Hlookup. apply (fixed_source_substitution natModel (fun _ => 0) phi sigma b c n base).
  - intro i. rewrite !numeral_natModel. apply Hlookup.
  - rewrite code_relation_natModel, sf_expression_value. reflexivity.
  - rewrite code_relation_natModel, sf_expression_value. reflexivity.
Qed.

Theorem standard_source_substitution_exact {ff}
    (phi : @Core.form sig_empty ZFSignature.ZF_pred_sig full_operators ff)
    sigma b c n base v :
  (forall i, substitution_lookup natModel b c n base i (sf_index (sigma i))) ->
  (numerical_substitution natModel (sf_encode phi) b c n base v <->
   v = sf_encode (subst_form sigma phi)).
Proof.
  intro Hlookup. pose proof (standard_source_substitution phi sigma b c n base Hlookup) as H.
  split.
  - intro Hv. exact (numerical_substitution_functional natModel (sf_encode phi)
      b c n base v _ Hv H).
  - intro E. now subst v.
Qed.

Lemma substitution_singleton_tail M b c i :
  substitution_lookup M b c (succM M (zeroM M)) (zeroM M) (succM M i) i.
Proof.
  apply substitution_lookup_outside.
  - intro H. apply (coding_not_lt_zero M i).
    exact (proj1 (coding_lt_succ_cancel M i (zeroM M)) H).
  - exists i. split; now rewrite ?Arithmetic.add_succ, coding_add_zero.
Qed.

Theorem fixed_source_singleton_substitution {ff} M rho
    (phi : @Core.form sig_empty ZFSignature.ZF_pred_sig full_operators ff)
    (t : sf_term) b c f v :
  substitution_lookup M b c (succM M (zeroM M)) (zeroM M) (zeroM M)
    (code_numeral M (sf_index t)) ->
  code_relation M rho (sf_expression phi) f ->
  code_relation M rho (sf_expression (subst_form (t .: var) phi)) v ->
  numerical_substitution M f b c (succM M (zeroM M)) (zeroM M) v.
Proof.
  intros Hhead Hf Hv. apply (fixed_source_substitution M rho phi (t .: var)
    b c (succM M (zeroM M)) (zeroM M) f v); [|exact Hf|exact Hv].
  intros [|i]; [exact Hhead|]. cbn [scons sf_index code_numeral].
  apply substitution_singleton_tail.
Qed.

Theorem standard_singleton_substitution_exact {ff}
    (phi : @Core.form sig_empty ZFSignature.ZF_pred_sig full_operators ff)
    (t : sf_term) b c v :
  substitution_lookup natModel b c 1 0 0 (sf_index t) ->
  (numerical_substitution natModel (sf_encode phi) b c 1 0 v <->
   v = sf_encode (subst_form (t .: var) phi)).
Proof.
  intro Hhead. apply (standard_source_substitution_exact phi (t .: var)).
  intros [|i]; [exact Hhead|]. cbn [scons sf_index].
  apply (substitution_singleton_tail natModel).
Qed.

Theorem standard_singleton_substitution_total {ff}
    (phi : @Core.form sig_empty ZFSignature.ZF_pred_sig full_operators ff) (t : sf_term) :
  exists b c, numerical_substitution natModel (sf_encode phi) b c 1 0
    (sf_encode (subst_form (t .: var) phi)).
Proof.
  destruct (substitution_singleton_total natModel (sf_index t)) as [b [c [Hhead Htail]]].
  exists b,c. apply (proj2 (standard_singleton_substitution_exact phi t b c _ Hhead)).
  reflexivity.
Qed.

Print Assumptions fixed_source_substitution.
Print Assumptions standard_source_substitution.
Print Assumptions standard_source_substitution_exact.
Print Assumptions fixed_source_singleton_substitution.
Print Assumptions standard_singleton_substitution_exact.
Print Assumptions standard_singleton_substitution_total.
