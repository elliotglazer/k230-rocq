(** Native-equality quotients for countably enumerated equivalence relations.
    Least representative indices avoid any quotient, propositional
    extensionality, functional extensionality or proof-irrelevance axiom.
    Classical choice selects the unique least index in a propositional proof. *)
From Stdlib Require Import Arith.PeanoNat Arith.Wf_nat Logic.ClassicalChoice
 Logic.Eqdep_dec.
Unset Implicit Arguments.

Lemma classical_nat_least (P : nat -> Prop) :
 (exists n, P n) -> exists n, P n /\ forall m, P m -> n <= m.
Proof.
 intros (n&Hn). revert Hn.
 induction n using lt_wf_ind. intro Hn.
 destruct (classic (exists m, m < n /\ P m)) as [(m&Hmn&Hm)|HNone].
 - exact (H m Hmn Hm).
 - exists n. split; [exact Hn|]. intros m Hm.
   destruct (Nat.le_gt_cases n m) as [Hle|Hlt]; [exact Hle|].
   exfalso. apply HNone. exists m. now split.
Qed.

Theorem countable_canonical_quotient (D : Type) (enumerate : nat -> D)
 (R : D -> D -> Prop) :
 (forall x, R x x) ->
 (forall x y, R x y -> R y x) ->
 (forall x y z, R x y -> R y z -> R x z) ->
 (forall x, exists n, enumerate n = x) ->
 exists (Q : Type) (project : D -> Q) (represent : Q -> D),
   (forall x y, R x y <-> project x = project y) /\
   (forall q, project (represent q) = q) /\
   (forall x, R x (represent (project x))).
Proof.
 intros HRefl HSym HTrans HEnum.
 assert (HMin : forall x, exists n,
   R x (enumerate n) /\ forall m, R x (enumerate m) -> n <= m).
 { intro x. apply classical_nat_least.
   destruct (HEnum x) as (n&En). exists n. rewrite En. exact (HRefl x). }
 destruct (@choice D nat
   (fun x n => R x (enumerate n) /\ forall m, R x (enumerate m) -> n <= m)
   HMin) as (canonical&HCanonical).
 assert (HIndex : forall x y, R x y <-> canonical x = canonical y).
 { intros x y. split.
   - intro Hxy. apply Nat.le_antisymm.
     + apply (proj2 (HCanonical x)).
       exact (HTrans x y (enumerate (canonical y)) Hxy (proj1 (HCanonical y))).
     + apply (proj2 (HCanonical y)).
       exact (HTrans y x (enumerate (canonical x)) (HSym x y Hxy) (proj1 (HCanonical x))).
   - intro E. pose proof (proj1 (HCanonical x)) as Hx.
     rewrite E in Hx.
     exact (HTrans x (enumerate (canonical y)) y Hx
       (HSym y (enumerate (canonical y)) (proj1 (HCanonical y)))). }
 assert (HIdempotent : forall x, canonical (enumerate (canonical x)) = canonical x).
 { intro x. symmetry. apply (proj1 (HIndex x (enumerate (canonical x)))).
   exact (proj1 (HCanonical x)). }
 set (Q := {n : nat | canonical (enumerate n) = n}).
 assert (QExt : forall u v : Q, proj1_sig u = proj1_sig v -> u = v).
 { intros [m Hm] [n Hn] E. simpl in E. subst n.
   assert (Hm = Hn) by (apply UIP_dec; exact Nat.eq_dec).
   now subst Hn. }
 set (project := fun x : D => (exist _ (canonical x) (HIdempotent x) : Q)).
 set (represent := fun q : Q => enumerate (proj1_sig q)).
 exists Q, project, represent. split.
 - intros x y. rewrite HIndex. split.
   + intro E. apply QExt. exact E.
   + intro E. exact (f_equal (@proj1_sig nat (fun n => canonical (enumerate n) = n)) E).
 - split.
   + intros [n Hn]. apply QExt. exact Hn.
   + intro x. exact (proj1 (HCanonical x)).
Qed.

Print Assumptions classical_nat_least.
Print Assumptions countable_canonical_quotient.
