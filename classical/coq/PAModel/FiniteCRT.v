(** Arithmetic congruence helpers for internal beta-sequence extension.
    No theorem here codes an externally supplied arbitrary function. *)
From PAModel Require Import Model Arithmetic FiniteCoding.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import setoid_ring.Ring.
Unset Implicit Arguments.

Section CRT.
Variable M : Model.
Local Notation D := (carrier M).
Local Notation Z := (zeroM M).
Local Notation S := (succM M).
Local Notation one := (S Z).
Local Infix "+" := (addM M).
Local Infix "*" := (mulM M).
Add Ring crt_model_ring : (model_semiring M).

Definition congruent (q x y : D) : Prop :=
  exists a b, x + q*a = y + q*b.

Lemma congruent_refl q x : congruent q x x.
Proof. exists Z, Z. reflexivity. Qed.

Lemma congruent_sym q x y : congruent q x y -> congruent q y x.
Proof. intros [a [b H]]. exists b, a. symmetry. exact H. Qed.

Lemma congruent_trans q x y z :
  congruent q x y -> congruent q y z -> congruent q x z.
Proof.
  intros [a [b H]] [c [d K]]. exists (a+c), (b+d).
  replace (x+q*(a+c)) with ((x+q*a)+q*c) by ring.
  rewrite H.
  replace ((y+q*b)+q*c) with ((y+q*c)+q*b) by ring.
  rewrite K. ring.
Qed.

Lemma congruent_add q x y z w :
  congruent q x y -> congruent q z w -> congruent q (x+z) (y+w).
Proof.
  intros [a [b H]] [c [d K]]. exists (a+c), (b+d).
  replace ((x+z)+q*(a+c)) with ((x+q*a)+(z+q*c)) by ring.
  rewrite H,K. ring.
Qed.

Lemma congruent_mul_r q x y z :
  congruent q x y -> congruent q (x*z) (y*z).
Proof.
  intros [a [b H]]. exists (a*z), (b*z).
  replace (x*z+q*(a*z)) with ((x+q*a)*z) by ring.
  rewrite H. ring.
Qed.

Lemma congruent_mul q x y z w :
  congruent q x y -> congruent q z w -> congruent q (x*z) (y*w).
Proof.
  intros H K. eapply congruent_trans.
  - apply congruent_mul_r. exact H.
  - replace (y*z) with (z*y) by ring.
    replace (y*w) with (w*y) by ring.
    apply congruent_mul_r. exact K.
Qed.

Lemma congruent_multiple q x y : congruent q (x+q*y) x.
Proof. exists Z, y. ring. Qed.

Lemma remainder_congruent x q r : remainder M x q r -> congruent q x r.
Proof.
  intros [_ [d ->]]. exists Z,d. ring.
Qed.

Lemma congruent_small q r s :
  coding_lt M r q -> coding_lt M s q -> congruent q r s -> r=s.
Proof.
  intros Hr Hs [a [b H]].
  replace (q*a) with (a*q) in H by ring.
  replace (q*b) with (b*q) in H by ring.
  exact (proj2 (@Peano.iFac_unique D (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) q a r b s Hr Hs H)).
Qed.

Lemma congruent_remainder x q r :
  coding_lt M Z q -> coding_lt M r q -> congruent q x r -> remainder M x q r.
Proof.
  intros Hq Hr H.
  destruct (remainder_total M x q Hq) as [s Hs].
  assert (K : congruent q s r).
  { eapply congruent_trans; [apply congruent_sym; apply remainder_congruent; exact Hs|exact H]. }
  assert (s=r) by (apply (congruent_small q s r (proj1 Hs) Hr K)).
  now subst s.
Qed.

Definition unit_modulo (a q : D) : Prop :=
  exists u, congruent q (a*u) one.

Lemma unit_one q : unit_modulo one q.
Proof. exists one. replace (one*one) with one by ring. apply congruent_refl. Qed.

Lemma unit_product a b q :
  unit_modulo a q -> unit_modulo b q -> unit_modulo (a*b) q.
Proof.
  intros [u Hu] [v Hv]. exists (u*v).
  replace ((a*b)*(u*v)) with ((a*u)*(b*v)) by ring.
  pose proof (congruent_mul q (a*u) one (b*v) one Hu Hv) as H.
  replace (one*one) with one in H by ring. exact H.
Qed.

Lemma crt_adjust m qpred b r : unit_modulo m (S qpred) ->
  exists b', congruent m b' b /\ congruent (S qpred) b' r.
Proof.
  intros [u Hu].
  exists (b+(m*u)*(r+qpred*b)). split.
  - replace (b+(m*u)*(r+qpred*b)) with (b+m*(u*(r+qpred*b))) by ring.
    apply congruent_multiple.
  - eapply congruent_trans.
    + apply congruent_add; [apply congruent_refl|].
      apply congruent_mul_r. exact Hu.
    + replace (b+one*(r+qpred*b)) with (r+(S qpred)*b).
      * apply congruent_multiple.
      * rewrite (succ_as_add M qpred). ring.
Qed.

(** The beta moduli have explicit inverses; no gcd or Bezout axiom is needed.
    The offset d may be any model element.  Positivity is unnecessary for this
    algebraic identity, and is imposed by the later bounded-index argument. *)
Lemma beta_unit_from_difference j d k :
  unit_modulo (beta_modulus M (d*k) j)
    (beta_modulus M (d*k) (j+d)).
Proof.
  set (i := j+d).
  set (c := d*k).
  set (q := beta_modulus M c i).
  set (p := (S i)*c).
  set (t := ((S i)*(S i))*k).
  set (w := one+((S i)*(S j))*k).
  assert (H : (beta_modulus M c j)*t+one=q*w).
  { unfold q,c,t,w,i,beta_modulus.
    rewrite (succ_as_add M ((S j)*(d*k))),
      (succ_as_add M ((S (j+d))*(d*k))),
      (succ_as_add M (j+d)), (succ_as_add M j).
    ring. }
  exists (t*p).
  exists one, (w*p).
  change ((beta_modulus M c j)*(t*p)+q*one=one+q*(w*p)).
  assert (HQ : q=p+one).
  { unfold q,p,beta_modulus. apply succ_as_add. }
  replace ((beta_modulus M c j)*(t*p)+q*one)
    with (((beta_modulus M c j)*t+one)*p+one) by (rewrite HQ; ring).
  rewrite H. ring.
Qed.

Lemma coding_lt_trans x y z :
  coding_lt M x y -> coding_lt M y z -> coding_lt M x z.
Proof.
  intros Hxy Hyz.
  apply (@Peano.lt_le_trans D (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) x z y Hxy).
  destruct Hyz as [d Hd]. exists (S d).
  change (z=y+S d).
  rewrite Hd, (succ_as_add M (y+d)), (succ_as_add M d). ring.
Qed.

Lemma coding_lt_succ_cases x y :
  coding_lt M x (S y) <-> coding_lt M x y \/ x=y.
Proof.
  exact (@Peano.lt_S D (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) x y).
Qed.

Lemma coding_lt_succ_cancel x y :
  coding_lt M (S x) (S y) <-> coding_lt M x y.
Proof.
  exact (@Peano.lt_SS D (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) x y).
Qed.

Lemma coding_not_lt_zero x : ~coding_lt M x Z.
Proof.
  exact (@Peano.nolessthen_zero D (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) x).
Qed.

Lemma beta_units_from_common_multiple n c :
  positive_common_multiple M n c ->
  forall i j, coding_lt M i j -> coding_lt M j (S n) ->
    unit_modulo (beta_modulus M c i) (beta_modulus M c j).
Proof.
  intros [_ Hdiv] i j [a Ha] Hjn.
  set (d := S a).
  assert (Hd : coding_lt M Z d) by (unfold d; apply coding_zero_lt_succ).
  assert (Hij : j=i+d).
  { rewrite Ha. unfold d. rewrite (succ_as_add M (i+a)), (succ_as_add M a). ring. }
  assert (Hdj : coding_lt M d (S j)).
  { exists i. rewrite Hij. f_equal. ring. }
  assert (Hdn : coding_lt M d (S n)).
  { destruct (proj1 (coding_lt_succ_cases d j) Hdj) as [Hdj' | ->]; [|exact Hjn].
    eapply coding_lt_trans; eassumption. }
  destruct (Hdiv d (conj Hd Hdn)) as [k Hk].
  rewrite Hij,Hk. apply beta_unit_from_difference.
Qed.

Lemma congruent_divisor q m x y :
  (exists d, m=q*d) -> congruent m x y -> congruent q x y.
Proof.
  intros [d ->] [a [b H]]. exists (d*a),(d*b).
  replace (q*(d*a)) with ((q*d)*a) by ring.
  replace (q*(d*b)) with ((q*d)*b) by ring. exact H.
Qed.

Definition crt_stage (c n : D) (R : D -> D -> Prop) (k : D) : Prop :=
  exists b m,
    (forall j, coding_lt M j k ->
      exists r, R j r /\ congruent (beta_modulus M c j) b r) /\
    (forall j, coding_lt M j k ->
      exists d, m=(beta_modulus M c j)*d) /\
    (forall j, coding_lt M k (S j) -> coding_lt M j n ->
      unit_modulo m (beta_modulus M c j)).

Lemma crt_stage_zero c n R : crt_stage c n R Z.
Proof.
  exists Z,one. split; [|split].
  - intros j Hj. exfalso. exact (coding_not_lt_zero j Hj).
  - intros j Hj. exfalso. exact (coding_not_lt_zero j Hj).
  - intros. apply unit_one.
Qed.

Lemma crt_stage_step c n R k :
  coding_lt M k n -> (exists r, R k r) ->
  (forall j, coding_lt M k j -> coding_lt M j n ->
    unit_modulo (beta_modulus M c k) (beta_modulus M c j)) ->
  crt_stage c n R k -> crt_stage c n R (S k).
Proof.
  intros Hkn [r Hr] Hpair [b [m [Hread [Hdiv Hunit]]]].
  destruct (crt_adjust m ((S k)*c) b r
    (Hunit k (coding_lt_succ M k) Hkn)) as [b' [Hbm Hbq]].
  exists b', (m*(beta_modulus M c k)). split; [|split].
  - intros j Hj. destruct (proj1 (coding_lt_succ_cases j k) Hj) as [Hjk | ->].
    + destruct (Hread j Hjk) as [s [Hs Hbs]]. exists s. split; [exact Hs|].
      eapply congruent_trans; [|exact Hbs].
      eapply congruent_divisor; [apply Hdiv;exact Hjk|exact Hbm].
    + exists r. split; assumption.
  - intros j Hj. destruct (proj1 (coding_lt_succ_cases j k) Hj) as [Hjk | ->].
    + destruct (Hdiv j Hjk) as [d Hd]. exists (d*(beta_modulus M c k)).
      rewrite Hd. ring.
    + exists m. ring.
  - intros j Hkj Hjn.
    apply (proj1 (coding_lt_succ_cancel k j)) in Hkj.
    apply unit_product.
    + apply Hunit; [apply coding_lt_succ_cases;left;exact Hkj|exact Hjn].
    + apply Hpair; assumption.
Qed.

(** A general accumulation lemma, with the induction gate explicit.
    This gate must be discharged by an actual PA formula for the chosen R;
    it is NOT an assumption of arbitrary-predicate induction or sequence
    coding in Model. *)
Lemma crt_accumulate_from_definability c n R :
  Definable1 M (fun k => coding_lt M k (S n) -> crt_stage c n R k) ->
  (forall j, coding_lt M j n -> exists r, R j r) ->
  (forall i j, coding_lt M i j -> coding_lt M j n ->
    unit_modulo (beta_modulus M c i) (beta_modulus M c j)) ->
  crt_stage c n R n.
Proof.
  intros Hdef Htotal Hpair.
  assert (H : forall k, coding_lt M k (S n) -> crt_stage c n R k).
  { apply (definable_induction M
      (fun k => coding_lt M k (S n) -> crt_stage c n R k) Hdef).
    - intros _. apply crt_stage_zero.
    - intros k IH Hbound.
      apply (proj1 (coding_lt_succ_cancel k n)) in Hbound.
      apply crt_stage_step.
      + exact Hbound.
      + apply Htotal. exact Hbound.
      + apply Hpair.
      + apply IH. apply coding_lt_succ_cases. left. exact Hbound. }
  apply H. apply coding_lt_succ.
Qed.

End CRT.
