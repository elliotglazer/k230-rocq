From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  NumericalProofs NumericalTraces CodeDescent CodeTags NamedSubstitutionRules NamedSubstitution.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Lemma named_atom_tag_bound eq : named_atom_tag eq < 4.
Proof. destruct eq;cbn;lia. Qed.
Lemma named_atom_tag_positive eq : named_atom_tag eq <> 0.
Proof. destruct eq;discriminate. Qed.
Lemma named_atom_tag_injective eq eq' : named_atom_tag eq=named_atom_tag eq' -> eq=eq'.
Proof. destruct eq,eq';cbn;congruence. Qed.
Lemma named_atom_tag_not_two eq : named_atom_tag eq<>2.
Proof. destruct eq;discriminate. Qed.
Lemma named_tag_nonzero M tag a b f : tag<>0 -> tagged_pair_graph M tag a b f -> f<>zeroM M.
Proof.
  intros Htag Hf Ef. subst f.
  exact (coding_not_lt_zero M a (proj1 (tagged_pair_positive_descent M a b (zeroM M) tag Htag Hf))).
Qed.
Lemma named_tag_conflict M tag tag' a b a' b' f :
  tag<4 -> tag'<4 -> tag<>tag' ->
  tagged_pair_graph M tag a b f -> tagged_pair_graph M tag' a' b' f -> False.
Proof.
  intros Ht Ht' Hne H H'.
  exact (Hne (proj1 (tagged_pair_decode_unique M tag tag' a b a' b' f Ht Ht' H H'))).
Qed.

Lemma named_substitution_identity_inv M f x v : named_substitution M f x x v -> v=f.
Proof.
  intro H. apply named_substitution_cases in H.
  destruct H as [[[Hstop Hv]|[Hxx Hatom]]|[[a [b [w [Hxx H]]]]|[a [b [a' [b' [Hxx H]]]]]]];
    try contradiction;exact Hv.
Qed.

Lemma named_substitution_zero_inv M x y v : named_substitution M (zeroM M) x y v -> v=zeroM M.
Proof.
  intro H. apply named_substitution_cases in H.
  destruct H as [[[Hstop Hv]|[Hxy [Ha|Ha]]]|[Hu|Hb]];[exact Hv| | | |].
  - destruct Ha as [a [b [a' [b' [Hf H]]]]].
    exfalso. exact (named_tag_nonzero M 1 a b (zeroM M) ltac:(lia) Hf eq_refl).
  - destruct Ha as [a [b [a' [b' [Hf H]]]]].
    exfalso. exact (named_tag_nonzero M 3 a b (zeroM M) ltac:(lia) Hf eq_refl).
  - destruct Hu as [a [b [w [Hxy [Hax [Hay [Hf H]]]]]]].
    exfalso. exact (named_tag_nonzero M 2 a b (zeroM M) ltac:(lia) Hf eq_refl).
  - destruct Hb as [a [b [a' [b' [Hxy [Hnz H]]]]]]. contradiction.
Qed.

Lemma named_substitution_binder_stop_inv M x b f y v :
  tagged_pair_graph M 2 x b f -> named_substitution M f x y v -> v=f.
Proof.
  intros Hf H. apply named_substitution_cases in H.
  destruct H as [[[Hstop Hv]|[Hxy [Ha|Ha]]]|[Hu|Hb]];[exact Hv| | | |].
  - destruct Ha as [a [d [a' [d' [Hf' H]]]]]. exfalso.
    exact (named_tag_conflict M 2 1 x b a d f ltac:(lia) ltac:(lia) ltac:(lia) Hf Hf').
  - destruct Ha as [a [d [a' [d' [Hf' H]]]]]. exfalso.
    exact (named_tag_conflict M 2 3 x b a d f ltac:(lia) ltac:(lia) ltac:(lia) Hf Hf').
  - destruct Hu as [a [d [w [Hxy [Hax [Hay [Hf' H]]]]]]].
    destruct (tagged_pair_decode_unique M 2 2 x b a d f ltac:(lia) ltac:(lia) Hf Hf') as [_ [Ex Ed]].
    congruence.
  - destruct Hb as [a [d [a' [d' [Hxy [Hnz [Hf' H]]]]]]]. exfalso.
    exact (named_tag_conflict M 2 0 x b a d f ltac:(lia) ltac:(lia) ltac:(lia) Hf Hf').
Qed.

Lemma named_substitution_atom_case_inv M eq eq' a b f x y v :
  tagged_pair_graph M (named_atom_tag eq) a b f -> named_sub_atom M eq' f x y v ->
  exists a' b',named_replace M x y a a' /\ named_replace M x y b b' /\
    tagged_pair_graph M (named_atom_tag eq) a' b' v.
Proof.
  intros Hf [c [d [a' [b' [Hf' [Ha [Hb Hv]]]]]]].
  destruct (tagged_pair_decode_unique M _ _ a b c d f
    (named_atom_tag_bound eq) (named_atom_tag_bound eq') Hf Hf') as [Et [Ea Eb]].
  apply named_atom_tag_injective in Et. subst eq' c d. exists a',b';auto.
Qed.

Theorem named_substitution_atom_inv M eq a b f x y v :
  x<>y -> tagged_pair_graph M (named_atom_tag eq) a b f -> named_substitution M f x y v ->
  exists a' b',named_replace M x y a a' /\ named_replace M x y b b' /\
    tagged_pair_graph M (named_atom_tag eq) a' b' v.
Proof.
  intros Hxy Hf H. apply named_substitution_cases in H.
  destruct H as [[[Hstop Hv]|[Hxy' [Ha|Ha]]]|[Hu|Hb]].
  - destruct Hstop as [Hxx|[Ef|[c Hf']]];[contradiction| |].
    + exfalso. exact (named_tag_nonzero M _ a b f (named_atom_tag_positive eq) Hf Ef).
    + exfalso. exact (named_tag_conflict M _ 2 a b x c f (named_atom_tag_bound eq)
        ltac:(lia) (named_atom_tag_not_two eq) Hf Hf').
  - eapply named_substitution_atom_case_inv; eassumption.
  - eapply named_substitution_atom_case_inv; eassumption.
  - destruct Hu as [c [d [w [Hxy' [Hcx [Hcy [Hf' H]]]]]]]. exfalso.
    exact (named_tag_conflict M _ 2 a b c d f (named_atom_tag_bound eq)
      ltac:(lia) (named_atom_tag_not_two eq) Hf Hf').
  - destruct Hb as [c [d [a' [b' [Hxy' [Hnz [Hf' H]]]]]]]. exfalso.
    exact (named_tag_conflict M _ 0 a b c d f (named_atom_tag_bound eq)
      ltac:(lia) (named_atom_tag_positive eq) Hf Hf').
Qed.

Theorem named_substitution_binary_inv M a b f x y v :
  x<>y -> f<>zeroM M -> tagged_pair_graph M 0 a b f -> named_substitution M f x y v ->
  exists a' b',named_substitution M a x y a' /\ named_substitution M b x y b' /\
    tagged_pair_graph M 0 a' b' v.
Proof.
  intros Hxy Hnz Hf H. apply named_substitution_cases in H.
  destruct H as [[[Hstop Hv]|[Hxy' [Ha|Ha]]]|[Hu|Hb]].
  - destruct Hstop as [Hxx|[Ef|[c Hf']]];try contradiction.
    exfalso. exact (named_tag_conflict M 0 2 a b x c f ltac:(lia) ltac:(lia) ltac:(lia) Hf Hf').
  - destruct Ha as [c [d [a' [b' [Hf' H]]]]]. exfalso.
    exact (named_tag_conflict M 0 1 a b c d f ltac:(lia) ltac:(lia) ltac:(lia) Hf Hf').
  - destruct Ha as [c [d [a' [b' [Hf' H]]]]]. exfalso.
    exact (named_tag_conflict M 0 3 a b c d f ltac:(lia) ltac:(lia) ltac:(lia) Hf Hf').
  - destruct Hu as [c [d [w [Hxy' [Hcx [Hcy [Hf' H]]]]]]]. exfalso.
    exact (named_tag_conflict M 0 2 a b c d f ltac:(lia) ltac:(lia) ltac:(lia) Hf Hf').
  - destruct Hb as [c [d [a' [b' [Hxy' [Hnz' [Hf' [Ha [Hb Hv]]]]]]]]].
    destruct (tagged_pair_decode_unique M 0 0 a b c d f ltac:(lia) ltac:(lia) Hf Hf') as [_ [Ea Eb]].
    subst c d. exists a',b';auto.
Qed.

Theorem named_substitution_unary_inv M a b f x y v :
  x<>y -> a<>x -> tagged_pair_graph M 2 a b f -> named_substitution M f x y v ->
  a<>y /\ exists w,named_substitution M b x y w /\ tagged_pair_graph M 2 a w v.
Proof.
  intros Hxy Hax Hf H. apply named_substitution_cases in H.
  destruct H as [[[Hstop Hv]|[Hxy' [Ha|Ha]]]|[Hu|Hb]].
  - destruct Hstop as [Hxx|[Ef|[c Hf']]];[contradiction| |].
    + exfalso. exact (named_tag_nonzero M 2 a b f ltac:(lia) Hf Ef).
    + destruct (tagged_pair_decode_unique M 2 2 a b x c f ltac:(lia) ltac:(lia) Hf Hf') as [_ [Ea Eb]].
      congruence.
  - destruct Ha as [c [d [a' [b' [Hf' H]]]]]. exfalso.
    exact (named_tag_conflict M 2 1 a b c d f ltac:(lia) ltac:(lia) ltac:(lia) Hf Hf').
  - destruct Ha as [c [d [a' [b' [Hf' H]]]]]. exfalso.
    exact (named_tag_conflict M 2 3 a b c d f ltac:(lia) ltac:(lia) ltac:(lia) Hf Hf').
  - destruct Hu as [c [d [w [Hxy' [Hcx [Hcy [Hf' [Hw Hv]]]]]]]].
    destruct (tagged_pair_decode_unique M 2 2 a b c d f ltac:(lia) ltac:(lia) Hf Hf') as [_ [Ea Eb]].
    subst c d. split;[exact Hcy|]. exists w;auto.
  - destruct Hb as [c [d [a' [b' [Hxy' [Hnz' [Hf' H]]]]]]]. exfalso.
    exact (named_tag_conflict M 2 0 a b c d f ltac:(lia) ltac:(lia) ltac:(lia) Hf Hf').
Qed.

Local Opaque holds named_substitution_formula.
Lemma named_substitution_functional_definable M : Definable1 M
  (fun f => forall x y v w,named_substitution M f x y v -> named_substitution M f x y w -> v=w).
Proof.
  exists (∀∀∀∀ (named_substitution_formula $4 $3 $2 $1 →
    named_substitution_formula $4 $3 $2 $0 → ($1 == $0))),(fun _ => zeroM M).
  intro f. repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite named_substitution_formula_correct. reflexivity.
Qed.

Theorem named_substitution_functional M f x y v w :
  named_substitution M f x y v -> named_substitution M f x y w -> v=w.
Proof.
  revert f x y v w. apply (formula_code_induction M
    (fun f => forall x y v w,named_substitution M f x y v -> named_substitution M f x y w -> v=w)).
  - apply named_substitution_functional_definable.
  - intros x y v w Hv Hw.
    rewrite (named_substitution_zero_inv M x y v Hv),(named_substitution_zero_inv M x y w Hw). reflexivity.
  - intros a b f Hf x y v w Hv Hw.
    destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
      (fun ax H rho => axioms M ax rho H) x y) as [->|Hxy].
    + rewrite (named_substitution_identity_inv M f y v Hv),(named_substitution_identity_inv M f y w Hw). reflexivity.
    + destruct (named_substitution_atom_inv M false a b f x y v Hxy Hf Hv) as [a' [b' [Ha [Hb Hout]]]].
      destruct (named_substitution_atom_inv M false a b f x y w Hxy Hf Hw) as [a'' [b'' [Ha' [Hb' Hout']]]].
      pose proof (named_replace_functional M x y a a' a'' Ha Ha') as Ea.
      pose proof (named_replace_functional M x y b b' b'' Hb Hb') as Eb.
      subst a'' b''. eapply tagged_pair_functional;eassumption.
  - intros a b f Hf x y v w Hv Hw.
    destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
      (fun ax H rho => axioms M ax rho H) x y) as [->|Hxy].
    + rewrite (named_substitution_identity_inv M f y v Hv),(named_substitution_identity_inv M f y w Hw). reflexivity.
    + destruct (named_substitution_atom_inv M true a b f x y v Hxy Hf Hv) as [a' [b' [Ha [Hb Hout]]]].
      destruct (named_substitution_atom_inv M true a b f x y w Hxy Hf Hw) as [a'' [b'' [Ha' [Hb' Hout']]]].
      pose proof (named_replace_functional M x y a a' a'' Ha Ha') as Ea.
      pose proof (named_replace_functional M x y b b' b'' Hb Hb') as Eb.
      subst a'' b''. eapply tagged_pair_functional;eassumption.
  - intros a b f Hnz Hf IHa IHb x y v w Hv Hw.
    destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
      (fun ax H rho => axioms M ax rho H) x y) as [->|Hxy].
    + rewrite (named_substitution_identity_inv M f y v Hv),(named_substitution_identity_inv M f y w Hw). reflexivity.
    + destruct (named_substitution_binary_inv M a b f x y v Hxy Hnz Hf Hv) as [a' [b' [Ha [Hb Hout]]]].
      destruct (named_substitution_binary_inv M a b f x y w Hxy Hnz Hf Hw) as [a'' [b'' [Ha' [Hb' Hout']]]].
      pose proof (IHa x y a' a'' Ha Ha') as Ea. pose proof (IHb x y b' b'' Hb Hb') as Eb.
      subst a'' b''. eapply tagged_pair_functional;eassumption.
  - intros a b f Hf IHb x y v w Hv Hw.
    destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
      (fun ax H rho => axioms M ax rho H) x y) as [->|Hxy].
    + rewrite (named_substitution_identity_inv M f y v Hv),(named_substitution_identity_inv M f y w Hw). reflexivity.
    + destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
        (fun ax H rho => axioms M ax rho H) a x) as [->|Hax].
      * rewrite (named_substitution_binder_stop_inv M x b f y v Hf Hv),
          (named_substitution_binder_stop_inv M x b f y w Hf Hw). reflexivity.
      * destruct (named_substitution_unary_inv M a b f x y v Hxy Hax Hf Hv) as [_ [a' [Ha Hout]]].
        destruct (named_substitution_unary_inv M a b f x y w Hxy Hax Hf Hw) as [_ [a'' [Ha' Hout']]].
        pose proof (IHb x y a' a'' Ha Ha') as Ea. subst a''.
        eapply tagged_pair_functional;eassumption.
Qed.
