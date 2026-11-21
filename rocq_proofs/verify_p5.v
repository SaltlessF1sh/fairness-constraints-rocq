From Stdlib Require Import Bool List Arith Lia Classical.
Import ListNotations.

(* ========================================================================= *)
(* Formal Verification in Rocq (Coq) of the ~3-QBF <-> Classifier Universal  *)
(* Fairness Reduction (Pi_3^P-completeness of P5, closing the Open Problem   *)
(* of Section 7 / Proposition 28 of Cooper & Bousdira, CP 2026).             *)
(* ========================================================================= *)

Definition lit := (nat * bool)%type.
Definition clause := list lit.
Definition cnf := list clause.

Definition eval_lit (assign : nat -> bool) (l : lit) : bool :=
  Bool.eqb (assign (fst l)) (snd l).

Fixpoint eval_clause (assign : nat -> bool) (c : clause) : bool :=
  match c with
  | [] => false
  | l :: rest => eval_lit assign l || eval_clause assign rest
  end.

Fixpoint eval_cnf (assign : nat -> bool) (phi : cnf) : bool :=
  match phi with
  | [] => true
  | c :: rest => eval_clause assign c && eval_cnf assign rest
  end.

Definition cnf_bounded (n : nat) (phi : cnf) : Prop :=
  forall c, In c phi -> forall l, In l c -> fst l < n.

Lemma eval_clause_ext_bounded : forall n c f g,
  (forall l, In l c -> fst l < n) ->
  (forall k, k < n -> f k = g k) ->
  eval_clause f c = eval_clause g c.
Proof.
  intros n c f g Hc Hext.
  induction c as [|l cs IHc]; simpl; [reflexivity|].
  f_equal.
  - unfold eval_lit. rewrite Hext; [reflexivity | apply Hc; left; reflexivity].
  - apply IHc. intros l' Hl'. apply Hc; right; exact Hl'.
Qed.

Lemma eval_cnf_ext_bounded : forall n phi f g,
  cnf_bounded n phi ->
  (forall k, k < n -> f k = g k) ->
  eval_cnf f phi = eval_cnf g phi.
Proof.
  intros n phi f g Hbnd Hext.
  induction phi as [|c rest IH]; simpl; [reflexivity|].
  f_equal.
  - apply (eval_clause_ext_bounded n c f g); [|exact Hext].
    intros l Hl. apply (Hbnd c (or_introl eq_refl) l Hl).
  - apply IH. intros c' Hc' l Hl. apply (Hbnd c' (or_intror Hc') l Hl).
Qed.

Definition combine3 (r q : nat) (X Y Z : nat -> bool) (k : nat) : bool :=
  if k <? r then X k
  else if k <? r + q then Y (k - r)
  else Z (k - (r + q)).

Lemma combine3_ext : forall r q s X1 X2 Y1 Y2 Z1 Z2 k,
  k < r + q + s ->
  (forall i, i < r -> X1 i = X2 i) ->
  (forall j, j < q -> Y1 j = Y2 j) ->
  (forall m, m < s -> Z1 m = Z2 m) ->
  combine3 r q X1 Y1 Z1 k = combine3 r q X2 Y2 Z2 k.
Proof.
  intros r q s X1 X2 Y1 Y2 Z1 Z2 k Hk HX HY HZ.
  unfold combine3.
  destruct (Nat.ltb_spec k r); [apply HX; lia|].
  destruct (Nat.ltb_spec k (r + q)); [apply HY; lia|].
  apply HZ; lia.
Qed.

Definition three_qbf (r q : nat) (phi : cnf) : Prop :=
  exists X : nat -> bool, forall Y : nat -> bool, exists Z : nat -> bool,
    eval_cnf (combine3 r q X Y Z) phi = true.

Record Inst := mkInst {
  fd : bool;
  fXp : nat -> bool;
  fXm : nat -> bool;
  fp : bool;
  fYp : nat -> bool;
  fYm : nat -> bool;
  fZ : nat -> bool
}.

Record Sub := mkSub {
  sd : bool;
  sXp : nat -> bool;
  sXm : nat -> bool;
  sp : bool;
  sYp : nat -> bool;
  sYm : nat -> bool;
  sZ : nat -> bool
}.

(* In P5 reduction, P = {d} is the unique protected feature. *)
Definition is_unfair_P5 (T : Sub) : Prop := sd T = true.

Definition agrees_on (r q s : nat) (w x : Inst) (S : Sub) : Prop :=
  (sd S = true -> fd w = fd x) /\
  (forall i, i < r -> sXp S i = true -> fXp w i = fXp x i) /\
  (forall i, i < r -> sXm S i = true -> fXm w i = fXm x i) /\
  (sp S = true -> fp w = fp x) /\
  (forall j, j < q -> sYp S j = true -> fYp w j = fYp x j) /\
  (forall j, j < q -> sYm S j = true -> fYm w j = fYm x j) /\
  (forall k, k < s -> sZ S k = true -> fZ w k = fZ x k).

Lemma agrees_on_refl : forall r q s x S, agrees_on r q s x x S.
Proof.
  intros r q s x S. repeat split; intros; reflexivity.
Qed.

Definition sub_le (r q s : nat) (S1 S2 : Sub) : Prop :=
  (sd S1 = true -> sd S2 = true) /\
  (forall i, i < r -> sXp S1 i = true -> sXp S2 i = true) /\
  (forall i, i < r -> sXm S1 i = true -> sXm S2 i = true) /\
  (sp S1 = true -> sp S2 = true) /\
  (forall j, j < q -> sYp S1 j = true -> sYp S2 j = true) /\
  (forall j, j < q -> sYm S1 j = true -> sYm S2 j = true) /\
  (forall k, k < s -> sZ S1 k = true -> sZ S2 k = true).

Definition sub_strict_lt (r q s : nat) (S1 S2 : Sub) : Prop :=
  sub_le r q s S1 S2 /\
  ((sd S2 = true /\ sd S1 = false) \/
   (exists i, i < r /\ sXp S2 i = true /\ sXp S1 i = false) \/
   (exists i, i < r /\ sXm S2 i = true /\ sXm S1 i = false) \/
   (sp S2 = true /\ sp S1 = false) \/
   (exists j, j < q /\ sYp S2 j = true /\ sYp S1 j = false) \/
   (exists j, j < q /\ sYm S2 j = true /\ sYm S1 j = false) \/
   (exists k, k < s /\ sZ S2 k = true /\ sZ S1 k = false)).

Lemma sub_le_trans : forall r q s A B C,
  sub_le r q s A B -> sub_le r q s B C -> sub_le r q s A C.
Proof.
  intros r q s A B C [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]] [G1 [G2 [G3 [G4 [G5 [G6 G7]]]]]].
  repeat split; intros; auto.
Qed.

Lemma agrees_sub_le : forall r q s w x S1 S2,
  sub_le r q s S1 S2 -> agrees_on r q s w x S2 -> agrees_on r q s w x S1.
Proof.
  intros r q s w x S1 S2 [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]] [G1 [G2 [G3 [G4 [G5 [G6 G7]]]]]].
  repeat split; intros; auto.
Qed.

Fixpoint forall_nat (n : nat) (P : nat -> bool) : bool :=
  match n with
  | 0 => true
  | S m => P m && forall_nat m P
  end.

Lemma forall_nat_iff : forall n P,
  forall_nat n P = true <-> (forall i, i < n -> P i = true).
Proof.
  induction n as [|m IH]; intro P; simpl.
  - split; [intros _ i Hi; lia | intros _; reflexivity].
  - rewrite Bool.andb_true_iff, IH. split.
    + intros [Hm Hrest] i Hi.
      destruct (Nat.eq_dec i m); [subst; exact Hm | apply Hrest; lia].
    + intro H. split; [apply H; lia | intros i Hi; apply H; lia].
Qed.

Lemma forall_nat_true : forall n P,
  (forall i, i < n -> P i = true) -> forall_nat n P = true.
Proof. intros n P. apply (proj2 (forall_nat_iff n P)). Qed.

Lemma forall_nat_elim : forall n P,
  forall_nat n P = true -> forall i, i < n -> P i = true.
Proof. intros n P. apply (proj1 (forall_nat_iff n P)). Qed.

Fixpoint exists_nat (n : nat) (P : nat -> bool) : bool :=
  match n with
  | 0 => false
  | S m => P m || exists_nat m P
  end.

Lemma exists_nat_iff : forall n P,
  exists_nat n P = true <-> (exists i, i < n /\ P i = true).
Proof.
  induction n as [|m IH]; intro P; simpl.
  - split; [discriminate | intros [i [Hi _]]; lia].
  - rewrite Bool.orb_true_iff, IH. split.
    + intros [Hm | [i [Hi Hp]]]; [exists m; split; [lia | exact Hm] | exists i; split; [lia | exact Hp]].
    + intros [i [Hi Hp]]. destruct (Nat.eq_dec i m); [subst; left; exact Hp | right; exists i; split; [lia | exact Hp]].
Qed.

Lemma exists_nat_true : forall n P i,
  i < n -> P i = true -> exists_nat n P = true.
Proof.
  intros n P i Hi Hp. apply (proj2 (exists_nat_iff n P)). exists i; split; assumption.
Qed.

Lemma exists_nat_false_elim : forall n P,
  exists_nat n P = false -> forall i, i < n -> P i = false.
Proof.
  intros n P H i Hi.
  destruct (P i) eqn:E; [|reflexivity].
  exfalso. pose proof (exists_nat_true n P i Hi E) as Ht. rewrite H in Ht. discriminate.
Qed.

Definition x_ok (r : nat) (w : Inst) : bool :=
  forall_nat r (fun i => fXp w i || fXm w i).

Definition x_not11 (r : nat) (w : Inst) : bool :=
  forall_nat r (fun i => negb (fXp w i && fXm w i)).

Definition y_not11 (q : nat) (w : Inst) : bool :=
  forall_nat q (fun j => negb (fYp w j && fYm w j)).

Definition all_Y_true (q : nat) (w : Inst) : bool :=
  forall_nat q (fun j => fYp w j && fYm w j).

Definition dummy_body (r q s : nat) (w : Inst) : bool :=
  forall_nat r (fun i => fXp w i && fXm w i) &&
  forall_nat q (fun j => negb (fYp w j) && negb (fYm w j)) &&
  forall_nat s (fun k => negb (fZ w k)).

Definition C_p5 (r q s : nat) (w : Inst) : bool :=
  if fd w then
    all_Y_true q w && (if x_ok r w then fp w else true)
  else
    if fp w then x_not11 r w && y_not11 q w
    else dummy_body r q s w.

Definition kappa_p5 (r q : nat) (phi : cnf) (w : Inst) : bool :=
  if fd w then x_ok r w
  else if fp w then
    if exists_nat r (fun i => negb (fXp w i) && negb (fXm w i)) ||
       exists_nat q (fun j => negb (fYp w j) && negb (fYm w j))
    then false
    else negb (eval_cnf (combine3 r q (fXp w) (fYp w) (fZ w)) phi)
  else false.

(* Literal Definition 14: Constrained FTU *)
Definition constrained_ftu (r q s : nat) (phi : cnf) : Prop :=
  forall u v : Inst,
    C_p5 r q s u = true ->
    C_p5 r q s v = true ->
    (forall i, i < r -> fXp u i = fXp v i) ->
    (forall i, i < r -> fXm u i = fXm v i) ->
    fp u = fp v ->
    (forall j, j < q -> fYp u j = fYp v j) ->
    (forall j, j < q -> fYm u j = fYm v j) ->
    (forall k, k < s -> fZ u k = fZ v k) ->
    kappa_p5 r q phi u = kappa_p5 r q phi v.

(* Literal Definition 3: Weak AXp and AXp *)
Definition weak_axp (r q s : nat) (phi : cnf) (x : Inst) (S : Sub) : Prop :=
  forall w : Inst, C_p5 r q s w = true -> agrees_on r q s w x S ->
    kappa_p5 r q phi w = kappa_p5 r q phi x.

Definition is_axp (r q s : nat) (phi : cnf) (x : Inst) (S : Sub) : Prop :=
  weak_axp r q s phi x S /\
  forall S' : Sub, sub_strict_lt r q s S' S -> ~ weak_axp r q s phi x S'.

(* Literal Definition 4: PI-explanation *)
Definition strictly_subsumes (r q s : nat) (x : Inst) (T S : Sub) : Prop :=
  (forall u : Inst, C_p5 r q s u = true -> agrees_on r q s u x S -> agrees_on r q s u x T) /\
  (exists v : Inst, C_p5 r q s v = true /\ agrees_on r q s v x T /\ ~ agrees_on r q s v x S).

Definition is_pi (r q s : nat) (phi : cnf) (x : Inst) (S : Sub) : Prop :=
  is_axp r q s phi x S /\
  forall T : Sub, is_axp r q s phi x T -> ~ strictly_subsumes r q s x T S.

(* Literal Definition 15: Classifier Universal Fairness *)
Definition cls_univ_fair (r q s : nat) (phi : cnf) : Prop :=
  forall x : Inst, C_p5 r q s x = true ->
    forall T : Sub, is_pi r q s phi x T -> ~ is_unfair_P5 T.

(* Weight helper for finite AXp extraction *)
Fixpoint sum_bool (n : nat) (f : nat -> bool) : nat :=
  match n with
  | 0 => 0
  | S m => (if f m then 1 else 0) + sum_bool m f
  end.

Definition sub_weight (r q s : nat) (S : Sub) : nat :=
  (if sd S then 1 else 0) +
  sum_bool r (sXp S) + sum_bool r (sXm S) +
  (if sp S then 1 else 0) +
  sum_bool q (sYp S) + sum_bool q (sYm S) + sum_bool s (sZ S).

Lemma sum_bool_le : forall n f1 f2,
  (forall i, i < n -> f1 i = true -> f2 i = true) ->
  sum_bool n f1 <= sum_bool n f2.
Proof.
  induction n as [|m IH]; intros f1 f2 H; simpl; [lia|].
  assert (Hm : (if f1 m then 1 else 0) <= (if f2 m then 1 else 0)).
  { destruct (f1 m) eqn:E1; [rewrite (H m ltac:(lia) E1); lia | destruct (f2 m); lia]. }
  assert (Hr : sum_bool m f1 <= sum_bool m f2) by (apply IH; intros i Hi; apply H; lia).
  lia.
Qed.

Lemma sum_bool_lt : forall n f1 f2 i0,
  (forall i, i < n -> f1 i = true -> f2 i = true) ->
  i0 < n -> f2 i0 = true -> f1 i0 = false ->
  sum_bool n f1 < sum_bool n f2.
Proof.
  induction n as [|m IH]; intros f1 f2 i0 Hle Hi0 H2 H1; simpl; [lia|].
  destruct (Nat.eq_dec i0 m).
  - subst. rewrite H2, H1.
    assert (Hr : sum_bool m f1 <= sum_bool m f2) by (apply sum_bool_le; intros i Hi; apply Hle; lia).
    lia.
  - assert (Hm : (if f1 m then 1 else 0) <= (if f2 m then 1 else 0)).
    { destruct (f1 m) eqn:E1; [rewrite (Hle m ltac:(lia) E1); lia | destruct (f2 m); lia]. }
    assert (Hr : sum_bool m f1 < sum_bool m f2) by (apply (IH f1 f2 i0); [intros i Hi; apply Hle; lia | lia | exact H2 | exact H1]).
    lia.
Qed.

Lemma sub_weight_lt : forall r q s S1 S2,
  sub_strict_lt r q s S1 S2 -> sub_weight r q s S1 < sub_weight r q s S2.
Proof.
  intros r q s S1 S2 [[H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]] Hlt].
  unfold sub_weight.
  assert (W1 : (if sd S1 then 1 else 0) <= (if sd S2 then 1 else 0)).
  { destruct (sd S1) eqn:E; [rewrite (H1 eq_refl); lia | destruct (sd S2); lia]. }
  assert (W2 : sum_bool r (sXp S1) <= sum_bool r (sXp S2)) by (apply sum_bool_le; exact H2).
  assert (W3 : sum_bool r (sXm S1) <= sum_bool r (sXm S2)) by (apply sum_bool_le; exact H3).
  assert (W4 : (if sp S1 then 1 else 0) <= (if sp S2 then 1 else 0)).
  { destruct (sp S1) eqn:E; [rewrite (H4 eq_refl); lia | destruct (sp S2); lia]. }
  assert (W5 : sum_bool q (sYp S1) <= sum_bool q (sYp S2)) by (apply sum_bool_le; exact H5).
  assert (W6 : sum_bool q (sYm S1) <= sum_bool q (sYm S2)) by (apply sum_bool_le; exact H6).
  assert (W7 : sum_bool s (sZ S1) <= sum_bool s (sZ S2)) by (apply sum_bool_le; exact H7).
  destruct Hlt as [[Ha Hb] | [[i [Hi [Ha Hb]]] | [[i [Hi [Ha Hb]]] | [[Ha Hb] |
                 [[j [Hj [Ha Hb]]] | [[j [Hj [Ha Hb]]] | [k [Hk [Ha Hb]]]]]]]]].
  - rewrite Ha, Hb in *; lia.
  - pose proof (sum_bool_lt r (sXp S1) (sXp S2) i H2 Hi Ha Hb); lia.
  - pose proof (sum_bool_lt r (sXm S1) (sXm S2) i H3 Hi Ha Hb); lia.
  - rewrite Ha, Hb in *; lia.
  - pose proof (sum_bool_lt q (sYp S1) (sYp S2) j H5 Hj Ha Hb); lia.
  - pose proof (sum_bool_lt q (sYm S1) (sYm S2) j H6 Hj Ha Hb); lia.
  - pose proof (sum_bool_lt s (sZ S1) (sZ S2) k H7 Hk Ha Hb); lia.
Qed.

Lemma weak_axp_has_axp : forall r q s phi x S,
  weak_axp r q s phi x S ->
  exists S' : Sub, sub_le r q s S' S /\ is_axp r q s phi x S'.
Proof.
  intros r q s phi x S HS.
  remember (sub_weight r q s S) as w eqn:Hw.
  revert S Hw HS.
  induction w as [w IH] using lt_wf_ind.
  intros S Hw HS.
  destruct (classic (is_axp r q s phi x S)) as [Haxp | Hnot].
  - exists S. split; [repeat split; intros; auto | exact Haxp].
  - unfold is_axp in Hnot.
    apply not_and_or in Hnot. destruct Hnot as [Hbad | Hnotmin]; [contradiction|].
    apply not_all_ex_not in Hnotmin. destruct Hnotmin as [S1 HS1].
    apply imply_to_and in HS1. destruct HS1 as [Hlt Hnotweak].
    apply NNPP in Hnotweak.
    assert (Hw1 : sub_weight r q s S1 < w).
    { subst w. apply sub_weight_lt; exact Hlt. }
    destruct (IH (sub_weight r q s S1) Hw1 S1 eq_refl Hnotweak) as [S' [Hle' Haxp']].
    exists S'. split; [|exact Haxp'].
    apply (sub_le_trans r q s S' S1 S Hle' (proj1 Hlt)).
Qed.

Lemma strictly_subsumes_weak_refute_pi : forall r q s phi x T S,
  weak_axp r q s phi x S ->
  strictly_subsumes r q s x S T ->
  ~ is_pi r q s phi x T.
Proof.
  intros r q s phi x T S HwS Hsub [_ Hno].
  destruct (weak_axp_has_axp r q s phi x S HwS) as [S' [Hle Haxp']].
  apply (Hno S' Haxp').
  destruct Hsub as [H1 [v [HvC [HvS HvnotT]]]].
  split.
  - intros u Hu HT. apply (agrees_sub_le r q s u x S' S Hle). apply H1; assumption.
  - exists v. split; [exact HvC | split; [apply (agrees_sub_le r q s v x S' S Hle); exact HvS | exact HvnotT]].
Qed.

(* ========================================================================= *)
(* Constrained FTU holds unconditionally when q >= 1 and phi is bounded.     *)
(* ========================================================================= *)

Lemma C_p5_fd_from_N : forall r q s u v,
  1 <= q ->
  C_p5 r q s u = true ->
  C_p5 r q s v = true ->
  fYp u 0 = fYp v 0 ->
  fYm u 0 = fYm v 0 ->
  fd u = fd v.
Proof.
  intros r q s u v Hq Hu Hv HY HYb.
  destruct (fd u) eqn:Edu; destruct (fd v) eqn:Edv; try reflexivity.
  - exfalso. unfold C_p5 in Hu, Hv. rewrite Edu in Hu. rewrite Edv in Hv.
    apply Bool.andb_true_iff in Hu. destruct Hu as [HallU _]. unfold all_Y_true in HallU.
    pose proof (forall_nat_elim q _ HallU 0 ltac:(lia)) as HU0. simpl in HU0.
    apply Bool.andb_true_iff in HU0. destruct HU0 as [HYu HYbu].
    rewrite HYu in HY. rewrite HYbu in HYb.
    destruct (fp v).
    + apply Bool.andb_true_iff in Hv. destruct Hv as [_ Hyn]. unfold y_not11 in Hyn.
      pose proof (forall_nat_elim q _ Hyn 0 ltac:(lia)) as HV0. simpl in HV0.
      rewrite <- HY, <- HYb in HV0. discriminate.
    + unfold dummy_body in Hv.
      apply Bool.andb_true_iff in Hv. destruct Hv as [Hv1 _].
      apply Bool.andb_true_iff in Hv1. destruct Hv1 as [_ Hyn].
      pose proof (forall_nat_elim q _ Hyn 0 ltac:(lia)) as HV0. simpl in HV0.
      apply Bool.andb_true_iff in HV0. destruct HV0 as [HYv _].
      rewrite <- HY in HYv. discriminate.
  - exfalso. unfold C_p5 in Hu, Hv. rewrite Edu in Hu. rewrite Edv in Hv.
    apply Bool.andb_true_iff in Hv. destruct Hv as [HallV _]. unfold all_Y_true in HallV.
    pose proof (forall_nat_elim q _ HallV 0 ltac:(lia)) as HV0. simpl in HV0.
    apply Bool.andb_true_iff in HV0. destruct HV0 as [HYv HYbv].
    rewrite HYv in HY. rewrite HYbv in HYb.
    destruct (fp u).
    + apply Bool.andb_true_iff in Hu. destruct Hu as [_ Hyn]. unfold y_not11 in Hyn.
      pose proof (forall_nat_elim q _ Hyn 0 ltac:(lia)) as HU0. simpl in HU0.
      rewrite HY, HYb in HU0. discriminate.
    + unfold dummy_body in Hu.
      apply Bool.andb_true_iff in Hu. destruct Hu as [Hu1 _].
      apply Bool.andb_true_iff in Hu1. destruct Hu1 as [_ Hyn].
      pose proof (forall_nat_elim q _ Hyn 0 ltac:(lia)) as HU0. simpl in HU0.
      apply Bool.andb_true_iff in HU0. destruct HU0 as [HYu _].
      rewrite HY in HYu. discriminate.
Qed.

Lemma forall_nat_ext : forall n P Q,
  (forall i, i < n -> P i = Q i) -> forall_nat n P = forall_nat n Q.
Proof.
  induction n as [|m IH]; intros P Q H; simpl; [reflexivity|].
  rewrite (H m ltac:(lia)), (IH P Q (fun i Hi => H i ltac:(lia))). reflexivity.
Qed.

Lemma exists_nat_ext : forall n P Q,
  (forall i, i < n -> P i = Q i) -> exists_nat n P = exists_nat n Q.
Proof.
  induction n as [|m IH]; intros P Q H; simpl; [reflexivity|].
  rewrite (H m ltac:(lia)), (IH P Q (fun i Hi => H i ltac:(lia))). reflexivity.
Qed.

Theorem p5_constrained_ftu : forall r q s phi,
  1 <= q ->
  cnf_bounded (r + q + s) phi ->
  constrained_ftu r q s phi.
Proof.
  intros r q s phi Hq Hbnd u v Hu Hv HA HB Hp HY HYb HZ.
  assert (Hd : fd u = fd v) by (apply (C_p5_fd_from_N r q s u v Hq Hu Hv (HY 0 ltac:(lia)) (HYb 0 ltac:(lia)))).
  unfold kappa_p5. rewrite Hd.
  destruct (fd v).
  - unfold x_ok. apply forall_nat_ext. intros i Hi. rewrite (HA i Hi), (HB i Hi). reflexivity.
  - rewrite Hp. destruct (fp v); [|reflexivity].
    assert (HexR : exists_nat r (fun i => negb (fXp u i) && negb (fXm u i)) =
                   exists_nat r (fun i => negb (fXp v i) && negb (fXm v i))).
    { apply exists_nat_ext. intros i Hi. rewrite (HA i Hi), (HB i Hi). reflexivity. }
    assert (HexQ : exists_nat q (fun j => negb (fYp u j) && negb (fYm u j)) =
                   exists_nat q (fun j => negb (fYp v j) && negb (fYm v j))).
    { apply exists_nat_ext. intros j Hj. rewrite (HY j Hj), (HYb j Hj). reflexivity. }
    rewrite HexR, HexQ.
    destruct (exists_nat r _ || exists_nat q _); [reflexivity|].
    f_equal.
    apply (eval_cnf_ext_bounded (r + q + s) phi _ _ Hbnd).
    intros k Hk. apply (combine3_ext r q s _ _ _ _ _ _ k Hk HA HY HZ).
Qed.

(* ========================================================================= *)
(* Witness instances and helpers                                             *)
(* ========================================================================= *)

Definition x_star : Inst :=
  mkInst true (fun _ => true) (fun _ => true) true (fun _ => true) (fun _ => true) (fun _ => true).

Lemma C_p5_x_star : forall r q s, C_p5 r q s x_star = true.
Proof.
  intros r q s. unfold C_p5, x_star, all_Y_true. simpl.
  destruct (x_ok r _); rewrite Bool.andb_true_r; apply forall_nat_true; intros; reflexivity.
Qed.

Lemma kappa_p5_x_star : forall r q phi, kappa_p5 r q phi x_star = true.
Proof.
  intros r q phi. unfold kappa_p5, x_star, x_ok. simpl.
  apply forall_nat_true; intros; reflexivity.
Qed.

Definition inst_dummy : Inst :=
  mkInst false (fun _ => true) (fun _ => true) false (fun _ => false) (fun _ => false) (fun _ => false).

Lemma C_p5_dummy : forall r q s, C_p5 r q s inst_dummy = true.
Proof.
  intros r q s. unfold C_p5, inst_dummy, dummy_body. simpl.
  rewrite !Bool.andb_true_iff. repeat split; apply forall_nat_true; intros; reflexivity.
Qed.

Lemma kappa_p5_dummy : forall r q phi, kappa_p5 r q phi inst_dummy = false.
Proof.
  intros r q phi. reflexivity.
Qed.

Definition inst_d0_p1 (X Y Z : nat -> bool) : Inst :=
  mkInst false X (fun i => negb (X i)) true Y (fun j => negb (Y j)) Z.

Lemma C_p5_d0_p1 : forall r q s X Y Z, C_p5 r q s (inst_d0_p1 X Y Z) = true.
Proof.
  intros r q s X Y Z. unfold C_p5, inst_d0_p1, x_not11, y_not11. simpl.
  rewrite Bool.andb_true_iff. split; apply forall_nat_true; intros k _; [destruct (X k) | destruct (Y k)]; reflexivity.
Qed.

Lemma kappa_p5_d0_p1 : forall r q phi X Y Z,
  kappa_p5 r q phi (inst_d0_p1 X Y Z) = negb (eval_cnf (combine3 r q X Y Z) phi).
Proof.
  intros r q phi X Y Z. unfold kappa_p5, inst_d0_p1. simpl.
  assert (Hr : exists_nat r (fun i => negb (X i) && negb (negb (X i))) = false).
  { induction r as [|m IH]; simpl; [reflexivity | destruct (X m); simpl; exact IH]. }
  assert (Hq : exists_nat q (fun j => negb (Y j) && negb (negb (Y j))) = false).
  { induction q as [|m IH]; simpl; [reflexivity | destruct (Y m); simpl; exact IH]. }
  rewrite Hr, Hq. reflexivity.
Qed.

Lemma neg_three_qbf_elim : forall r q phi,
  ~ three_qbf r q phi ->
  forall X : nat -> bool, exists Y : nat -> bool, forall Z : nat -> bool,
    eval_cnf (combine3 r q X Y Z) phi = false.
Proof.
  intros r q phi Hnqbf X.
  apply NNPP. intro Hno. apply Hnqbf. exists X. intro Y.
  apply NNPP. intro HnoZ. apply Hno. exists Y. intro Z.
  destruct (eval_cnf (combine3 r q X Y Z) phi) eqn:E; [exfalso; apply HnoZ; exists Z; exact E | reflexivity].
Qed.

(* ========================================================================= *)
(* Direction 1: ~ three_qbf -> cls_univ_fair                                 *)
(* ========================================================================= *)

(* Case 1: fd x = true /\ x_ok r x = true *)
Lemma neg_three_qbf_case_d1_true : forall r q s phi x T,
  cnf_bounded (r + q + s) phi ->
  ~ three_qbf r q phi ->
  C_p5 r q s x = true ->
  fd x = true ->
  x_ok r x = true ->
  is_unfair_P5 T ->
  ~ is_pi r q s phi x T.
Proof.
  intros r q s phi x T Hbnd Hnqbf HxC Hxd Hxok HTunf HTpi.
  destruct (proj1 HTpi) as [HTw _].
  assert (Hxkappa : kappa_p5 r q phi x = true) by (unfold kappa_p5; rewrite Hxd; exact Hxok).
  assert (Hpx : fp x = true).
  { unfold C_p5 in HxC. rewrite Hxd, Hxok in HxC.
    apply Bool.andb_true_iff in HxC. exact (proj2 HxC). }
  assert (HYx : all_Y_true q x = true).
  { unfold C_p5 in HxC. rewrite Hxd in HxC.
    apply Bool.andb_true_iff in HxC. exact (proj1 HxC). }
  assert (HAB : forall i, i < r -> (sXp T i = true /\ fXp x i = true) \/ (sXm T i = true /\ fXm x i = true)).
  { intros i Hi.
    destruct (classic ((sXp T i = true /\ fXp x i = true) \/ (sXm T i = true /\ fXm x i = true))) as [H|Hnot]; [exact H|].
    exfalso.
    set (w := mkInst true (fun k => if k =? i then false else fXp x k)
                          (fun k => if k =? i then false else fXm x k)
                          (fp x) (fYp x) (fYm x) (fZ x)).
    assert (HwC : C_p5 r q s w = true).
    { unfold C_p5, w. change (fd _) with true. change (all_Y_true q _) with (all_Y_true q x).
      rewrite HYx, Hpx. simpl. match goal with |- (if ?c then true else true) = true => destruct c; reflexivity end. }
    assert (Hwag : agrees_on r q s w x T).
    { repeat split; try (intros; reflexivity); unfold w; simpl.
      - rewrite Hxd; reflexivity.
      - intros k Hk HkA. destruct (Nat.eqb_spec k i); [|reflexivity].
        subst. destruct (fXp x i) eqn:E; [exfalso; apply Hnot; left; auto | reflexivity].
      - intros k Hk HkB. destruct (Nat.eqb_spec k i); [|reflexivity].
        subst. destruct (fXm x i) eqn:E; [exfalso; apply Hnot; right; auto | reflexivity]. }
    pose proof (HTw w HwC Hwag) as Hkw.
    rewrite Hxkappa in Hkw. unfold kappa_p5, w, x_ok in Hkw. simpl in Hkw.
    pose proof (forall_nat_elim r _ Hkw i Hi) as Hi0. simpl in Hi0.
    rewrite Nat.eqb_refl in Hi0. discriminate. }
  set (X := fun i => sXp T i && fXp x i).
  set (S_core := mkSub true X (fun i => negb (X i)) false (fun _ => false) (fun _ => false) (fun _ => false)).
  assert (Hsub_core : sub_le r q s S_core T).
  { repeat split; simpl; intros; try discriminate.
    - exact HTunf.
    - unfold X in H0. apply Bool.andb_true_iff in H0. exact (proj1 H0).
    - unfold X in H0. apply Bool.negb_true_iff in H0.
      destruct (HAB i H) as [[HA1 HA2] | [HB1 _]]; [rewrite HA1, HA2 in H0; discriminate | exact HB1]. }
  destruct (neg_three_qbf_elim r q phi Hnqbf X) as [Ystar HYstar].
  set (S := mkSub false X (fun i => negb (X i)) true Ystar (fun j => negb (Ystar j)) (fun _ => false)).
  unfold all_Y_true in HYx.
  assert (HwS : weak_axp r q s phi x S).
  { intros w HwC [_ [WA [WB [Wp [WY [WYb _]]]]]].
    rewrite Hxkappa.
    assert (HwX : forall i, i < r -> (X i = true -> fXp w i = fXp x i /\ fXp x i = true) /\
                                      (X i = false -> fXm w i = fXm x i /\ fXm x i = true)).
    { intros i Hi. unfold X. split; intro EX.
      - split; [apply WA; [exact Hi | unfold X; exact EX] | apply Bool.andb_true_iff in EX; exact (proj2 EX)].
      - destruct (HAB i Hi) as [[HA1 HA2] | [HB1 HB2]]; [rewrite HA1, HA2 in EX; discriminate|].
        split; [apply WB; [exact Hi | unfold sXm, S; unfold X in *; rewrite EX; reflexivity] | exact HB2]. }
    destruct (fd w) eqn:Ewd.
    - unfold kappa_p5. rewrite Ewd. unfold x_ok. apply forall_nat_true. intros i Hi.
      destruct (X i) eqn:EX.
      + destruct (HwX i Hi) as [H1 _]. destruct (H1 EX) as [-> ->]. reflexivity.
      + destruct (HwX i Hi) as [_ H2]. destruct (H2 EX) as [-> ->]. apply Bool.orb_true_r.
    - unfold C_p5 in HwC. rewrite Ewd in HwC.
      assert (Hpw : fp w = true) by (rewrite (Wp eq_refl), Hpx; reflexivity).
      rewrite Hpw in HwC. apply Bool.andb_true_iff in HwC. destruct HwC as [Hxn Hyn].
      unfold x_not11 in Hxn. unfold y_not11 in Hyn.
      assert (HwA : forall i, i < r -> fXp w i = X i).
      { intros i Hi. destruct (X i) eqn:EX.
        - destruct (HwX i Hi) as [H1 _]. destruct (H1 EX) as [-> ->]. reflexivity.
        - destruct (HwX i Hi) as [_ H2]. destruct (H2 EX) as [HwB HBt].
          pose proof (forall_nat_elim r _ Hxn i Hi) as Hni. simpl in Hni.
          rewrite HwB, HBt, Bool.andb_true_r in Hni.
          destruct (fXp w i); [discriminate | reflexivity]. }
      assert (HwY : forall j, j < q -> fYp w j = Ystar j).
      { intros j Hj. destruct (Ystar j) eqn:EY.
        - rewrite (WY j Hj EY).
          pose proof (forall_nat_elim q _ HYx j Hj) as Hj1.
          apply Bool.andb_true_iff in Hj1. exact (proj1 Hj1).
        - assert (Hwyb : fYm w j = true).
          { rewrite (WYb j Hj); [|unfold sYm, S; rewrite EY; reflexivity].
            pose proof (forall_nat_elim q _ HYx j Hj) as Hj1.
            apply Bool.andb_true_iff in Hj1. exact (proj2 Hj1). }
          pose proof (forall_nat_elim q _ Hyn j Hj) as Hnj. simpl in Hnj.
          rewrite Hwyb, Bool.andb_true_r in Hnj.
          destruct (fYp w j); [discriminate | reflexivity]. }
      assert (HwB : forall i, i < r -> fXm w i = negb (X i)).
      { intros i Hi. destruct (X i) eqn:EX.
        - assert (HwAi : fXp w i = true) by (rewrite HwA; auto).
          pose proof (forall_nat_elim r _ Hxn i Hi) as Hni. simpl in Hni.
          rewrite HwAi, Bool.andb_true_l in Hni. destruct (fXm w i); [discriminate | reflexivity].
        - destruct (HwX i Hi) as [_ H2]. destruct (H2 EX) as [-> ->]. reflexivity. }
      assert (HwYb : forall j, j < q -> fYm w j = negb (Ystar j)).
      { intros j Hj. destruct (Ystar j) eqn:EY.
        - assert (HwYj : fYp w j = true) by (rewrite HwY; auto).
          pose proof (forall_nat_elim q _ Hyn j Hj) as Hnj. simpl in Hnj.
          rewrite HwYj, Bool.andb_true_l in Hnj. destruct (fYm w j); [discriminate | reflexivity].
        - rewrite (WYb j Hj); [|unfold sYm, S; rewrite EY; reflexivity].
          pose proof (forall_nat_elim q _ HYx j Hj) as Hj1.
          apply Bool.andb_true_iff in Hj1. exact (proj2 Hj1). }
      unfold kappa_p5. rewrite Ewd, Hpw.
      assert (HexR : exists_nat r (fun i => negb (fXp w i) && negb (fXm w i)) = false).
      { destruct (exists_nat r _) eqn:Er; [|reflexivity].
        apply (proj1 (exists_nat_iff _ _)) in Er. destruct Er as [i [Hi H0]].
        rewrite HwA, HwB in H0; [|exact Hi|exact Hi]. destruct (X i); discriminate. }
      assert (HexQ : exists_nat q (fun j => negb (fYp w j) && negb (fYm w j)) = false).
      { destruct (exists_nat q _) eqn:Eq; [|reflexivity].
        apply (proj1 (exists_nat_iff _ _)) in Eq. destruct Eq as [j [Hj H0]].
        rewrite HwY, HwYb in H0; [|exact Hj|exact Hj]. destruct (Ystar j); discriminate. }
      rewrite HexR, HexQ. simpl.
      rewrite (eval_cnf_ext_bounded (r + q + s) phi _ (combine3 r q X Ystar (fZ w)) Hbnd);
      [ rewrite (HYstar (fZ w)); reflexivity
      | intros k Hk; apply (combine3_ext r q s _ _ _ _ _ _ k Hk HwA HwY (fun _ _ => eq_refl)) ]. }
  apply (strictly_subsumes_weak_refute_pi r q s phi x T S HwS); [|exact HTpi].
  split.
  - intros u Hu HT.
    pose proof (agrees_sub_le r q s u x S_core T Hsub_core HT) as [_ [HuA [HuB _]]].
    simpl in HuA, HuB. unfold X in HuA, HuB.
    assert (Hud : fd u = true) by (destruct HT as [HTd _]; rewrite (HTd HTunf); exact Hxd).
    unfold C_p5 in Hu. rewrite Hud in Hu. apply Bool.andb_true_iff in Hu. destruct Hu as [HYu Hrest].
    unfold all_Y_true in HYu.
    assert (Huok : x_ok r u = true).
    { unfold x_ok. apply forall_nat_true. intros i Hi.
      destruct (sXp T i && fXp x i) eqn:EX.
      - rewrite (HuA i Hi EX), (proj2 (proj1 (Bool.andb_true_iff _ _) EX)). reflexivity.
      - rewrite (HuB i Hi). 2: { rewrite EX; reflexivity. }
        destruct (HAB i Hi) as [[HA1 HA2] | [_ HB2]]; [rewrite HA1, HA2 in EX; discriminate|].
        rewrite HB2. apply Bool.orb_true_r. }
    rewrite Huok in Hrest.
    repeat split; simpl; intros; try discriminate.
    + exact (HuA i H H0).
    + exact (HuB i H H0).
    + rewrite Hrest, Hpx. reflexivity.
    + pose proof (forall_nat_elim q _ HYu j H) as Huj. apply Bool.andb_true_iff in Huj.
      pose proof (forall_nat_elim q _ HYx j H) as Hxj. apply Bool.andb_true_iff in Hxj.
      rewrite (proj1 Huj), (proj1 Hxj). reflexivity.
    + pose proof (forall_nat_elim q _ HYu j H) as Huj. apply Bool.andb_true_iff in Huj.
      pose proof (forall_nat_elim q _ HYx j H) as Hxj. apply Bool.andb_true_iff in Hxj.
      rewrite (proj2 Huj), (proj2 Hxj). reflexivity.
  - exists (inst_d0_p1 X Ystar (fun _ => false)). split; [apply C_p5_d0_p1 | split].
    + repeat split; simpl; intros; try discriminate.
      * assert (HX0 : X i = true) by exact H0. unfold X in H0. apply Bool.andb_true_iff in H0. rewrite HX0, (proj2 H0). reflexivity.
      * apply Bool.negb_true_iff in H0.
        destruct (HAB i H) as [[HA1 HA2] | [_ HB2]]; [unfold X in H0; rewrite HA1, HA2 in H0; discriminate|].
        rewrite HB2, H0. reflexivity.
      * symmetry. exact Hpx.
      * pose proof (forall_nat_elim q _ HYx j H) as Hxj. apply Bool.andb_true_iff in Hxj. rewrite (proj1 Hxj), H0. reflexivity.
      * pose proof (forall_nat_elim q _ HYx j H) as Hxj. apply Bool.andb_true_iff in Hxj. rewrite (proj2 Hxj), H0. reflexivity.
    + intro HagT. destruct HagT as [HTd _]. specialize (HTd HTunf). simpl in HTd. rewrite Hxd in HTd. discriminate.
Qed.

(* Case 2: fd x = true /\ x_ok r x = false *)
Lemma neg_three_qbf_case_d1_false : forall r q s phi x T,
  C_p5 r q s x = true ->
  fd x = true ->
  x_ok r x = false ->
  is_unfair_P5 T ->
  ~ is_pi r q s phi x T.
Proof.
  intros r q s phi x T HxC Hxd Hxok HTunf [[HTw HTmin] _].
  assert (Hxkappa : kappa_p5 r q phi x = false) by (unfold kappa_p5; rewrite Hxd; exact Hxok).
  assert (HYx : all_Y_true q x = true).
  { unfold C_p5 in HxC. rewrite Hxd in HxC. apply Bool.andb_true_iff in HxC. exact (proj1 HxC). }
  destruct (classic (fp x = false /\ sp T = true)) as [[Hpx Hsp] | Hnop].
  - set (Sp := mkSub false (fun _ => false) (fun _ => false) true (fun _ => false) (fun _ => false) (fun _ => false)).
    assert (Hlt : sub_strict_lt r q s Sp T).
    { repeat split; simpl; intros; try discriminate.
      - exact Hsp.
      - left. split; [exact HTunf | reflexivity]. }
    apply (HTmin Sp Hlt).
    intros w HwC [_ [_ [_ [Wp _]]]]. rewrite Hxkappa.
    assert (Hpw : fp w = false) by (rewrite (Wp eq_refl), Hpx; reflexivity).
    unfold kappa_p5. destruct (fd w) eqn:Ewd.
    + unfold C_p5 in HwC. rewrite Ewd in HwC. apply Bool.andb_true_iff in HwC. destruct HwC as [_ Hrest].
      destruct (x_ok r w); [rewrite Hrest in Hpw; discriminate | reflexivity].
    + rewrite Hpw. reflexivity.
  - assert (Hexi : exists i0, i0 < r /\ sXp T i0 = true /\ sXm T i0 = true /\ fXp x i0 = false /\ fXm x i0 = false).
    { apply NNPP. intro Hno.
      set (fXp' := fun i => if sXp T i then fXp x i else true).
      set (fXm' := fun i => if sXm T i then fXm x i else true).
      set (w := mkInst true fXp' fXm' true (fYp x) (fYm x) (fZ x)).
      assert (Hwok : x_ok r w = true).
      { unfold x_ok, w. simpl. apply forall_nat_true. intros i Hi.
        unfold fXp', fXm'. destruct (sXp T i) eqn:EA; destruct (sXm T i) eqn:EB; simpl.
        - destruct (fXp x i) eqn:Efa; [reflexivity|].
          destruct (fXm x i) eqn:Efb; [reflexivity|].
          exfalso. apply Hno. exists i; auto.
        - apply Bool.orb_true_r.
        - reflexivity.
        - reflexivity. }
      assert (HwC : C_p5 r q s w = true).
      { unfold C_p5. change (fd w) with true. change (all_Y_true q w) with (all_Y_true q x).
        rewrite Hwok, HYx. reflexivity. }
      assert (Hwag : agrees_on r q s w x T).
      { repeat split; unfold w; simpl; intros; try reflexivity.
        - rewrite Hxd; reflexivity.
        - unfold fXp'. rewrite H0. reflexivity.
        - unfold fXm'. rewrite H0. reflexivity.
        - destruct (fp x) eqn:Epx; [reflexivity | exfalso; apply Hnop; split; [reflexivity | exact H]]. }
      pose proof (HTw w HwC Hwag) as Hkw.
      rewrite Hxkappa in Hkw. unfold kappa_p5 in Hkw. change (fd w) with true in Hkw. rewrite Hwok in Hkw. discriminate. }
    destruct Hexi as [i0 [Hi0 [HA1 [HB1 [HA0 HB0]]]]].
    set (Si0 := mkSub false (fun i => i =? i0) (fun i => i =? i0) false (fun _ => false) (fun _ => false) (fun _ => false)).
    assert (Hlt : sub_strict_lt r q s Si0 T).
    { repeat split; simpl; intros; try discriminate.
      - apply Nat.eqb_eq in H0; subst; exact HA1.
      - apply Nat.eqb_eq in H0; subst; exact HB1.
      - left. split; [exact HTunf | reflexivity]. }
    apply (HTmin Si0 Hlt).
    intros w HwC [_ [WA [WB _]]]. rewrite Hxkappa.
    assert (HwA : fXp w i0 = false) by (rewrite (WA i0 Hi0 (Nat.eqb_refl i0)); exact HA0).
    assert (HwB : fXm w i0 = false) by (rewrite (WB i0 Hi0 (Nat.eqb_refl i0)); exact HB0).
    unfold kappa_p5. destruct (fd w) eqn:Ewd.
    + unfold x_ok. destruct (forall_nat r _) eqn:Eok; [|reflexivity].
      pose proof (forall_nat_elim r _ Eok i0 Hi0) as H0. simpl in H0. rewrite HwA, HwB in H0. discriminate.
    + destruct (fp w) eqn:Epw; [|reflexivity].
      assert (Hex : exists_nat r (fun i => negb (fXp w i) && negb (fXm w i)) = true).
      { apply (exists_nat_true r _ i0 Hi0). rewrite HwA, HwB. reflexivity. }
      rewrite Hex. reflexivity.
Qed.

(* Case 3: fd x = false /\ fp x = false (dummy) *)
Lemma neg_three_qbf_case_d0_p0 : forall r q s phi x T,
  1 <= r -> 1 <= q ->
  ~ three_qbf r q phi ->
  C_p5 r q s x = true ->
  fd x = false ->
  fp x = false ->
  is_unfair_P5 T ->
  ~ is_pi r q s phi x T.
Proof.
  intros r q s phi x T Hr Hq Hnqbf HxC Hxd Hxp HTunf HTpi.
  destruct HTpi as [[HTw HTmin] HTsub].
  assert (Hxkappa : kappa_p5 r q phi x = false) by (unfold kappa_p5; rewrite Hxd, Hxp; reflexivity).
  unfold C_p5, dummy_body in HxC. rewrite Hxd, Hxp in HxC.
  apply Bool.andb_true_iff in HxC. destruct HxC as [H1 HZx].
  apply Bool.andb_true_iff in H1. destruct H1 as [HABx HYx].
  assert (HxAB : forall i, i < r -> fXp x i = true /\ fXm x i = true).
  { intros i Hi. pose proof (forall_nat_elim r _ HABx i Hi) as H0.
    apply Bool.andb_true_iff in H0. exact H0. }
  assert (HxY : forall j, j < q -> fYp x j = false /\ fYm x j = false).
  { intros j Hj. pose proof (forall_nat_elim q _ HYx j Hj) as H0.
    apply Bool.andb_true_iff in H0. rewrite !Bool.negb_true_iff in H0. exact H0. }
  assert (HxZ : forall k, k < s -> fZ x k = false).
  { intros k Hk. pose proof (forall_nat_elim s _ HZx k Hk) as H0.
    rewrite Bool.negb_true_iff in H0. exact H0. }
  destruct (classic (exists j, j < q /\ (sYp T j = true \/ sYm T j = true))) as [[j0 [Hj0 [HY0|HYb0]]] | HnoY].
  - set (T' := mkSub false (sXp T) (sXm T) (sp T) (sYp T) (sYm T) (sZ T)).
    assert (Hlt : sub_strict_lt r q s T' T).
    { repeat split; simpl; intros; try discriminate; auto. }
    apply (HTmin T' Hlt).
    intros w HwC [_ [WA [WB [Wp [WY [WYb WZ]]]]]].
    apply HTw; [exact HwC|]. repeat split; simpl; intros; auto.
    destruct (fd w) eqn:Ewd; [|symmetry; exact Hxd].
    exfalso. unfold C_p5 in HwC. rewrite Ewd in HwC. apply Bool.andb_true_iff in HwC. destruct HwC as [Hall _].
    unfold all_Y_true in Hall. pose proof (forall_nat_elim q _ Hall j0 Hj0) as Hw0. simpl in Hw0. apply Bool.andb_true_iff in Hw0.
    rewrite (WY j0 Hj0 HY0), (proj1 (HxY j0 Hj0)) in Hw0. destruct Hw0 as [Hc _]; discriminate.
  - set (T' := mkSub false (sXp T) (sXm T) (sp T) (sYp T) (sYm T) (sZ T)).
    assert (Hlt : sub_strict_lt r q s T' T).
    { repeat split; simpl; intros; try discriminate; auto. }
    apply (HTmin T' Hlt).
    intros w HwC [_ [WA [WB [Wp [WY [WYb WZ]]]]]].
    apply HTw; [exact HwC|]. repeat split; simpl; intros; auto.
    destruct (fd w) eqn:Ewd; [|symmetry; exact Hxd].
    exfalso. unfold C_p5 in HwC. rewrite Ewd in HwC. apply Bool.andb_true_iff in HwC. destruct HwC as [Hall _].
    unfold all_Y_true in Hall. pose proof (forall_nat_elim q _ Hall j0 Hj0) as Hw0. simpl in Hw0. apply Bool.andb_true_iff in Hw0.
    rewrite (WYb j0 Hj0 HYb0), (proj2 (HxY j0 Hj0)) in Hw0. destruct Hw0 as [_ Hc]; discriminate.
  - set (Sp := mkSub false (fun _ => false) (fun _ => false) true (fun _ => false) (fun _ => false) (fun _ => false)).
    assert (HwSp : weak_axp r q s phi x Sp).
    { intros w HwC [_ [_ [_ [Wp _]]]]. rewrite Hxkappa.
      assert (Hpw : fp w = false) by (rewrite (Wp eq_refl), Hxp; reflexivity).
      unfold kappa_p5. destruct (fd w) eqn:Ewd.
      - unfold C_p5 in HwC. rewrite Ewd in HwC. apply Bool.andb_true_iff in HwC. destruct HwC as [_ Hrest].
        destruct (x_ok r w); [rewrite Hrest in Hpw; discriminate | reflexivity].
      - rewrite Hpw. reflexivity. }
    assert (HpiT : is_pi r q s phi x T) by (split; [split; assumption | assumption]).
    apply (strictly_subsumes_weak_refute_pi r q s phi x T Sp HwSp); [|exact HpiT].
    split.
    + intros u HuC HuT.
      assert (Hud : fd u = false) by (destruct HuT as [HTd _]; rewrite (HTd HTunf); exact Hxd).
      assert (Hpu : fp u = false).
      { destruct (fp u) eqn:Epu; [|reflexivity].
        exfalso.
        destruct (sp T) eqn:Esp.
        { destruct HuT as [_ [_ [_ [Wp _]]]]. rewrite (Wp Esp), Hxp in Epu. discriminate. }
        unfold C_p5 in HuC. rewrite Hud, Epu in HuC. apply Bool.andb_true_iff in HuC. destruct HuC as [Hxn _].
        unfold x_not11 in Hxn.
        assert (Hnotboth : forall i, i < r -> ~ (sXp T i = true /\ sXm T i = true)).
        { intros i Hi [HA1 HB1]. destruct HuT as [_ [WA [WB _]]].
          pose proof (forall_nat_elim r _ Hxn i Hi) as Hni. simpl in Hni.
          rewrite (WA i Hi HA1), (WB i Hi HB1), (proj1 (HxAB i Hi)), (proj2 (HxAB i Hi)) in Hni. discriminate. }
        set (X := fun i => sXp T i).
        destruct (neg_three_qbf_elim r q phi Hnqbf X) as [Ystar HYstar].
        set (w := inst_d0_p1 X Ystar (fun _ => false)).
        assert (HwC : C_p5 r q s w = true) by apply C_p5_d0_p1.
        assert (Hwag : agrees_on r q s w x T).
        { repeat split; unfold w, inst_d0_p1; simpl; intros; try reflexivity.
          - symmetry; exact Hxd.
          - unfold X. rewrite H0, (proj1 (HxAB i H)). reflexivity.
          - unfold X. destruct (sXp T i) eqn:EA; [exfalso; apply (Hnotboth i H (conj EA H0)) | rewrite (proj2 (HxAB i H)); reflexivity].
          - rewrite Esp in H; discriminate.
          - exfalso. apply HnoY. exists j; auto.
          - exfalso. apply HnoY. exists j; auto.
          - symmetry. exact (HxZ k H). }
        pose proof (HTw w HwC Hwag) as Hkw.
        unfold w in Hkw. rewrite Hxkappa, kappa_p5_d0_p1, (HYstar (fun _ => false)) in Hkw. discriminate. }
      repeat split; simpl; intros; try discriminate. rewrite Hpu, Hxp. reflexivity.
    + set (v := mkInst true (fun _ => false) (fun _ => false) false (fun _ => true) (fun _ => true) (fun _ => false)).
      assert (Hvok : x_ok r v = false).
      { unfold x_ok, v. destruct r as [|m]; [lia | reflexivity]. }
      exists v. split; [|split].
      * unfold C_p5. change (fd v) with true. rewrite Hvok. unfold v, all_Y_true. simpl. apply Bool.andb_true_iff; split; [apply forall_nat_true; intros; reflexivity | reflexivity].
      * repeat split; simpl; intros; try discriminate. symmetry. exact Hxp.
      * intro HagT. destruct HagT as [HTd _]. specialize (HTd HTunf). simpl in HTd. rewrite Hxd in HTd. discriminate.
Qed.

(* Case 4: fd x = false /\ fp x = true *)
Lemma neg_three_qbf_case_d0_p1 : forall r q s phi x T,
  1 <= q ->
  ~ three_qbf r q phi ->
  C_p5 r q s x = true ->
  fd x = false ->
  fp x = true ->
  is_unfair_P5 T ->
  ~ is_pi r q s phi x T.
Proof.
  intros r q s phi x T Hq Hnqbf HxC Hxd Hxp HTunf HTpi.
  destruct HTpi as [[HTw HTmin] HTsub].
  assert (HxC' : x_not11 r x = true /\ y_not11 q x = true).
  { unfold C_p5 in HxC. rewrite Hxd, Hxp in HxC. apply Bool.andb_true_iff in HxC. exact HxC. }
  destruct HxC' as [Hxn Hyn].
  unfold x_not11 in Hxn. unfold y_not11 in Hyn.
  (* Subcase 4a: If T contains any 0-bit of Y or Yb, dropping d preserves coverage *)
  destruct (classic (exists j, j < q /\ ((sYp T j = true /\ fYp x j = false) \/ (sYm T j = true /\ fYm x j = false))))
    as [[j0 [Hj0 [[HY1 HY0] | [HYb1 HYb0]]]] | HnoY0].
  - set (T' := mkSub false (sXp T) (sXm T) (sp T) (sYp T) (sYm T) (sZ T)).
    assert (Hlt : sub_strict_lt r q s T' T).
    { repeat split; simpl; intros; try discriminate; auto. }
    apply (HTmin T' Hlt).
    intros w HwC [_ [WA [WB [Wp [WY [WYb WZ]]]]]].
    apply HTw; [exact HwC|]. repeat split; simpl; intros; auto.
    destruct (fd w) eqn:Ewd; [|symmetry; exact Hxd].
    exfalso. unfold C_p5 in HwC. rewrite Ewd in HwC. apply Bool.andb_true_iff in HwC. destruct HwC as [Hall _].
    unfold all_Y_true in Hall. pose proof (forall_nat_elim q _ Hall j0 Hj0) as Hw0. simpl in Hw0. apply Bool.andb_true_iff in Hw0.
    rewrite (WY j0 Hj0 HY1), HY0 in Hw0. destruct Hw0 as [Hc _]; discriminate.
  - set (T' := mkSub false (sXp T) (sXm T) (sp T) (sYp T) (sYm T) (sZ T)).
    assert (Hlt : sub_strict_lt r q s T' T).
    { repeat split; simpl; intros; try discriminate; auto. }
    apply (HTmin T' Hlt).
    intros w HwC [_ [WA [WB [Wp [WY [WYb WZ]]]]]].
    apply HTw; [exact HwC|]. repeat split; simpl; intros; auto.
    destruct (fd w) eqn:Ewd; [|symmetry; exact Hxd].
    exfalso. unfold C_p5 in HwC. rewrite Ewd in HwC. apply Bool.andb_true_iff in HwC. destruct HwC as [Hall _].
    unfold all_Y_true in Hall. pose proof (forall_nat_elim q _ Hall j0 Hj0) as Hw0. simpl in Hw0. apply Bool.andb_true_iff in Hw0.
    rewrite (WYb j0 Hj0 HYb1), HYb0 in Hw0. destruct Hw0 as [_ Hc]; discriminate.
  - (* Now every fixed Y/Yb in T has value true at x *)
    assert (HY1bits : forall j, j < q -> (sYp T j = true -> fYp x j = true) /\ (sYm T j = true -> fYm x j = true)).
    { intros j Hj. split; intro Hs.
      - destruct (fYp x j) eqn:E; [reflexivity | exfalso; apply HnoY0; exists j; auto].
      - destruct (fYm x j) eqn:E; [reflexivity | exfalso; apply HnoY0; exists j; auto]. }
    destruct (kappa_p5 r q phi x) eqn:Hxkappa.
    + (* Subcase 4b: kappa(x) = true: dropping d keeps kappa = true everywhere! *)
      unfold kappa_p5 in Hxkappa. rewrite Hxd, Hxp in Hxkappa.
      destruct (exists_nat r _) eqn:Er0; [discriminate|].
      destruct (exists_nat q _) eqn:Eq0; [discriminate|].
      simpl in Hxkappa.
      (* Every pair i < r must have a 1-bit fixed by T *)
      assert (HAB1 : forall i, i < r -> (sXp T i = true /\ fXp x i = true) \/ (sXm T i = true /\ fXm x i = true)).
      { intros i Hi.
        destruct (classic ((sXp T i = true /\ fXp x i = true) \/ (sXm T i = true /\ fXm x i = true))) as [H|Hnot]; [exact H|].
        exfalso.
        set (w := mkInst false (fun k => if k =? i then false else fXp x k)
                               (fun k => if k =? i then false else fXm x k)
                               true (fYp x) (fYm x) (fZ x)).
        assert (HwC : C_p5 r q s w = true).
        { unfold C_p5, w, x_not11, y_not11. simpl. rewrite Bool.andb_true_iff. split; [|exact Hyn].
          apply forall_nat_true. intros k Hk. destruct (Nat.eqb_spec k i); [reflexivity | exact (forall_nat_elim r _ Hxn k Hk)]. }
        assert (Hwag : agrees_on r q s w x T).
        { repeat split; unfold w; simpl; intros; try reflexivity.
          - symmetry; exact Hxd.
          - destruct (Nat.eqb_spec i0 i); [subst; destruct (fXp x i) eqn:E; [exfalso; apply Hnot; left; auto | reflexivity] | reflexivity].
          - destruct (Nat.eqb_spec i0 i); [subst; destruct (fXm x i) eqn:E; [exfalso; apply Hnot; right; auto | reflexivity] | reflexivity].
          - symmetry; exact Hxp. }
        pose proof (HTw w HwC Hwag) as Hkw.
        unfold kappa_p5, w in Hkw. simpl in Hkw.
        assert (Hex : exists_nat r (fun k => negb (if k =? i then false else fXp x k) && negb (if k =? i then false else fXm x k)) = true).
        { apply (exists_nat_true r _ i Hi). rewrite Nat.eqb_refl. reflexivity. }
        rewrite Hex in Hkw. simpl in Hkw.
        unfold kappa_p5 in Hkw. rewrite Hxd, Hxp, Er0, Eq0 in Hkw. simpl in Hkw.
        rewrite Hxkappa in Hkw. discriminate. }
      set (T' := mkSub false (sXp T) (sXm T) (sp T) (sYp T) (sYm T) (sZ T)).
      assert (Hlt : sub_strict_lt r q s T' T).
      { repeat split; simpl; intros; try discriminate; auto. }
      apply (HTmin T' Hlt).
      intros w HwC [_ [WA [WB [Wp [WY [WYb WZ]]]]]].
      unfold kappa_p5 at 2. rewrite Hxd, Hxp, Er0, Eq0. simpl. rewrite Hxkappa.
      destruct (fd w) eqn:Ewd.
      * unfold kappa_p5. rewrite Ewd. unfold x_ok. apply forall_nat_true. intros i Hi.
        destruct (HAB1 i Hi) as [[HA1 HA2] | [HB1 HB2]].
        -- rewrite (WA i Hi HA1), HA2. reflexivity.
        -- rewrite (WB i Hi HB1), HB2. apply Bool.orb_true_r.
      * transitivity (kappa_p5 r q phi x);
        [apply HTw; [exact HwC|]; repeat split; simpl; intros; auto; rewrite Ewd, Hxd; reflexivity
        | unfold kappa_p5; rewrite Hxd, Hxp, Er0, Eq0; simpl; exact Hxkappa].
    + (* Subcase 4c: kappa(x) = false *)
      destruct (classic (exists j0, j0 < q /\ (sYp T j0 = true \/ sYm T j0 = true))) as [[j0 [Hj0 HY0]] | HnoY].
      * (* Flip Y/Yb in S *)
        set (S := mkSub false (sXp T) (sXm T) true (sYm T) (sYp T) (sZ T)).
        assert (HwS : weak_axp r q s phi x S).
        { intros w HwC [_ [WA [WB [Wp [WY [WYb WZ]]]]]].
          rewrite Hxkappa.
          assert (Hpw : fp w = true) by (rewrite (Wp eq_refl), Hxp; reflexivity).
          assert (Hwd : fd w = false).
          { destruct (fd w) eqn:Ewd; [|reflexivity]. exfalso.
            unfold C_p5 in HwC. rewrite Ewd in HwC. apply Bool.andb_true_iff in HwC. destruct HwC as [Hall _].
            unfold all_Y_true in Hall. pose proof (forall_nat_elim q _ Hall j0 Hj0) as Hw0. simpl in Hw0. apply Bool.andb_true_iff in Hw0.
            destruct HY0 as [HYt|HYbt].
            - assert (HYbf : fYm x j0 = false).
              { pose proof (forall_nat_elim q _ Hyn j0 Hj0) as Hxj. simpl in Hxj.
                rewrite (proj1 (HY1bits j0 Hj0) HYt) in Hxj. destruct (fYm x j0); [discriminate | reflexivity]. }
              rewrite (WYb j0 Hj0 HYt), HYbf in Hw0. destruct Hw0 as [_ Hc]; discriminate.
            - assert (HYf : fYp x j0 = false).
              { pose proof (forall_nat_elim q _ Hyn j0 Hj0) as Hxj. simpl in Hxj.
                rewrite (proj2 (HY1bits j0 Hj0) HYbt), Bool.andb_true_r in Hxj. destruct (fYp x j0); [discriminate | reflexivity]. }
              rewrite (WY j0 Hj0 HYbt), HYf in Hw0. destruct Hw0 as [Hc _]; discriminate. }
          destruct (classic (forall j, j < q -> (sYp T j = true -> fYp w j = fYp x j) /\ (sYm T j = true -> fYm w j = fYm x j)))
            as [Hmatch | Hmiss].
          - rewrite <- Hxkappa. apply HTw; [exact HwC|].
            repeat split; simpl; intros; auto; [rewrite Hwd, Hxd; reflexivity | exact (proj1 (Hmatch j H) H0) | exact (proj2 (Hmatch j H) H0)].
          - apply not_all_ex_not in Hmiss. destruct Hmiss as [j1 Hmiss].
            apply imply_to_and in Hmiss. destruct Hmiss as [Hj1 Hnot].
            unfold C_p5 in HwC. rewrite Hwd, Hpw in HwC. apply Bool.andb_true_iff in HwC. destruct HwC as [_ Hwyn].
            unfold kappa_p5. rewrite Hwd, Hpw.
            assert (HexQ : exists_nat q (fun j => negb (fYp w j) && negb (fYm w j)) = true).
            { apply not_and_or in Hnot. destruct Hnot as [Hnot|Hnot];
              apply imply_to_and in Hnot; destruct Hnot as [HTj Hdiff].
              - assert (Hxt : fYp x j1 = true) by exact (proj1 (HY1bits j1 Hj1) HTj).
                assert (Hwf : fYp w j1 = false) by (destruct (fYp w j1) eqn:Ew; [exfalso; apply Hdiff; congruence | reflexivity]).
                assert (Hxbf : fYm x j1 = false).
                { pose proof (forall_nat_elim q _ Hyn j1 Hj1) as Hxj. simpl in Hxj. rewrite Hxt in Hxj. destruct (fYm x j1); [discriminate | reflexivity]. }
                assert (Hwbf : fYm w j1 = false) by (rewrite (WYb j1 Hj1 HTj); exact Hxbf).
                apply (exists_nat_true q _ j1 Hj1). rewrite Hwf, Hwbf. reflexivity.
              - assert (Hxbt : fYm x j1 = true) by exact (proj2 (HY1bits j1 Hj1) HTj).
                assert (Hwbf : fYm w j1 = false) by (destruct (fYm w j1) eqn:Ew; [exfalso; apply Hdiff; congruence | reflexivity]).
                assert (Hxf : fYp x j1 = false).
                { pose proof (forall_nat_elim q _ Hyn j1 Hj1) as Hxj. simpl in Hxj. rewrite Hxbt, Bool.andb_true_r in Hxj. destruct (fYp x j1); [discriminate | reflexivity]. }
                assert (Hwf : fYp w j1 = false) by (rewrite (WY j1 Hj1 HTj); exact Hxf).
                apply (exists_nat_true q _ j1 Hj1). rewrite Hwf, Hwbf. reflexivity. }
            rewrite HexQ, Bool.orb_true_r. reflexivity. }
        assert (HpiT : is_pi r q s phi x T) by (split; [split; assumption | assumption]).
        apply (strictly_subsumes_weak_refute_pi r q s phi x T S HwS); [|exact HpiT].
        split.
        -- intros u HuC HuT.
           assert (Hud : fd u = false) by (destruct HuT as [HTd _]; rewrite (HTd HTunf); exact Hxd).
           assert (Hpu : fp u = true).
           { destruct (fp u) eqn:Epu; [reflexivity|]. exfalso.
             unfold C_p5, dummy_body in HuC. rewrite Hud, Epu in HuC.
             apply Bool.andb_true_iff in HuC. destruct HuC as [Hu1 _].
             apply Bool.andb_true_iff in Hu1. destruct Hu1 as [_ HuY].
             pose proof (forall_nat_elim q _ HuY j0 Hj0) as Hu0. simpl in Hu0. apply Bool.andb_true_iff in Hu0.
             destruct HuT as [_ [_ [_ [_ [WY [WYb _]]]]]].
             destruct HY0 as [HYt|HYbt].
             - rewrite (WY j0 Hj0 HYt), (proj1 (HY1bits j0 Hj0) HYt) in Hu0. destruct Hu0 as [Hc _]; discriminate.
             - rewrite (WYb j0 Hj0 HYbt), (proj2 (HY1bits j0 Hj0) HYbt) in Hu0. destruct Hu0 as [_ Hc]; discriminate. }
           unfold C_p5 in HuC. rewrite Hud, Hpu in HuC. apply Bool.andb_true_iff in HuC. destruct HuC as [_ Huyn].
           unfold y_not11 in Huyn.
           destruct HuT as [_ [WA [WB [_ [WY [WYb WZ]]]]]].
           repeat split; simpl; intros; try discriminate; try auto.
           ++ rewrite Hpu, Hxp. reflexivity.
           ++ assert (Huyb : fYm u j = true) by (rewrite (WYb j H H0); exact (proj2 (HY1bits j H) H0)).
              pose proof (forall_nat_elim q _ Huyn j H) as Huj. simpl in Huj. rewrite Huyb, Bool.andb_true_r in Huj.
              pose proof (forall_nat_elim q _ Hyn j H) as Hxj. simpl in Hxj. rewrite (proj2 (HY1bits j H) H0), Bool.andb_true_r in Hxj.
              destruct (fYp u j); destruct (fYp x j); try reflexivity; discriminate.
           ++ assert (Huy : fYp u j = true) by (rewrite (WY j H H0); exact (proj1 (HY1bits j H) H0)).
              pose proof (forall_nat_elim q _ Huyn j H) as Huj. simpl in Huj. rewrite Huy, Bool.andb_true_l in Huj.
              pose proof (forall_nat_elim q _ Hyn j H) as Hxj. simpl in Hxj. rewrite (proj1 (HY1bits j H) H0), Bool.andb_true_l in Hxj.
              destruct (fYm u j); destruct (fYm x j); try reflexivity; discriminate.
        -- set (v := mkInst false (fXp x) (fXm x) true
                            (fun j => if j =? j0 then false else fYp x j)
                            (fun j => if j =? j0 then false else fYm x j) (fZ x)).
           exists v. split; [|split].
           ++ unfold C_p5, v, x_not11, y_not11. simpl.
              rewrite Hxn. simpl.
              apply forall_nat_true. intros j Hj. destruct (Nat.eqb_spec j j0); [reflexivity | exact (forall_nat_elim q _ Hyn j Hj)].
           ++ repeat split; simpl; intros; try discriminate; try reflexivity.
              ** symmetry; exact Hxp.
              ** destruct (Nat.eqb_spec j j0); [|reflexivity].
                 subst j. pose proof (forall_nat_elim q _ Hyn j0 Hj0) as Hxj. simpl in Hxj.
                 rewrite (proj2 (HY1bits j0 Hj0) H0), Bool.andb_true_r in Hxj. destruct (fYp x j0); [discriminate | reflexivity].
              ** destruct (Nat.eqb_spec j j0); [|reflexivity].
                 subst j. pose proof (forall_nat_elim q _ Hyn j0 Hj0) as Hxj. simpl in Hxj.
                 rewrite (proj1 (HY1bits j0 Hj0) H0), Bool.andb_true_l in Hxj. destruct (fYm x j0); [discriminate | reflexivity].
           ++ intro HagT. destruct HagT as [_ [_ [_ [_ [WY [WYb _]]]]]].
              destruct HY0 as [HYt|HYbt].
              ** pose proof (WY j0 Hj0 HYt) as H0. unfold v in H0. simpl in H0. rewrite Nat.eqb_refl in H0.
                 rewrite (proj1 (HY1bits j0 Hj0) HYt) in H0. discriminate.
              ** pose proof (WYb j0 Hj0 HYbt) as H0. unfold v in H0. simpl in H0. rewrite Nat.eqb_refl in H0.
                 rewrite (proj2 (HY1bits j0 Hj0) HYbt) in H0. discriminate.
      * (* No Y or Yb in T *)
        destruct (classic (exists i0, i0 < r /\ sXp T i0 = true /\ sXm T i0 = true /\ fXp x i0 = false /\ fXm x i0 = false))
          as [[i0 [Hi0 [HA1 [HB1 [HA0 HB0]]]]] | Hnot00].
        -- set (Si0 := mkSub false (fun i => i =? i0) (fun i => i =? i0) false (fun _ => false) (fun _ => false) (fun _ => false)).
           assert (Hlt : sub_strict_lt r q s Si0 T).
           { repeat split; simpl; intros; try discriminate; auto.
             - apply Nat.eqb_eq in H0; subst; exact HA1.
             - apply Nat.eqb_eq in H0; subst; exact HB1. }
           apply (HTmin Si0 Hlt).
           intros w HwC [_ [WA [WB _]]]. rewrite Hxkappa.
           assert (HwA : fXp w i0 = false) by (rewrite (WA i0 Hi0 (Nat.eqb_refl i0)); exact HA0).
           assert (HwB : fXm w i0 = false) by (rewrite (WB i0 Hi0 (Nat.eqb_refl i0)); exact HB0).
           unfold kappa_p5. destruct (fd w) eqn:Ewd.
           ++ unfold x_ok. destruct (forall_nat r (fun i => fXp w i || fXm w i)) eqn:Eok; [|reflexivity].
              pose proof (forall_nat_elim r _ Eok i0 Hi0) as H0. simpl in H0. rewrite HwA, HwB in H0. discriminate.
           ++ destruct (fp w) eqn:Epw; [|reflexivity].
              assert (Hex : exists_nat r (fun i => negb (fXp w i) && negb (fXm w i)) = true).
              { apply (exists_nat_true r _ i0 Hi0). rewrite HwA, HwB. reflexivity. }
              rewrite Hex. reflexivity.
        -- set (X := fun i => if sXp T i then fXp x i else negb (fXm x i)).
           destruct (neg_three_qbf_elim r q phi Hnqbf X) as [Ystar HYstar].
           set (w := inst_d0_p1 X Ystar (fZ x)).
           assert (HwC : C_p5 r q s w = true) by apply C_p5_d0_p1.
           assert (Hwag : agrees_on r q s w x T).
           { repeat split; unfold w; simpl; intros; try reflexivity.
             - symmetry; exact Hxd.
             - unfold X. rewrite H0. reflexivity.
             - unfold X. destruct (sXp T i) eqn:EA.
               + destruct (fXp x i) eqn:Efa; destruct (fXm x i) eqn:Efb.
                 * pose proof (forall_nat_elim r _ Hxn i H) as Hni. simpl in Hni. rewrite Efa, Efb in Hni. discriminate.
                 * reflexivity.
                 * reflexivity.
                 * exfalso. apply Hnot00. exists i; auto.
               + rewrite Bool.negb_involutive. reflexivity.
             - symmetry; exact Hxp.
             - exfalso. apply HnoY. exists j; auto.
             - exfalso. apply HnoY. exists j; auto. }
           pose proof (HTw w HwC Hwag) as Hkw.
           unfold w in Hkw. rewrite Hxkappa, kappa_p5_d0_p1, (HYstar (fZ x)) in Hkw. discriminate.
Qed.

Theorem neg_three_qbf_implies_cls_univ_fair : forall r q s phi,
  1 <= r -> 1 <= q ->
  cnf_bounded (r + q + s) phi ->
  ~ three_qbf r q phi ->
  cls_univ_fair r q s phi.
Proof.
  intros r q s phi Hr Hq Hbnd Hnqbf.
  intros x HxC T HTpi HTunf.
  destruct (fd x) eqn:Exd.
  + destruct (x_ok r x) eqn:Exok.
    * exact (neg_three_qbf_case_d1_true r q s phi x T Hbnd Hnqbf HxC Exd Exok HTunf HTpi).
    * exact (neg_three_qbf_case_d1_false r q s phi x T HxC Exd Exok HTunf HTpi).
  + destruct (fp x) eqn:Exp.
    * exact (neg_three_qbf_case_d0_p1 r q s phi x T Hq Hnqbf HxC Exd Exp HTunf HTpi).
    * exact (neg_three_qbf_case_d0_p0 r q s phi x T Hr Hq Hnqbf HxC Exd Exp HTunf HTpi).
Qed.

(* ========================================================================= *)
(* Direction 2: three_qbf -> ~ cls_univ_fair                                 *)
(* ========================================================================= *)

Theorem three_qbf_implies_not_cls_univ_fair : forall r q s phi,
  three_qbf r q phi ->
  ~ cls_univ_fair r q s phi.
Proof.
  intros r q s phi [X HX] Huniv.
  set (T := mkSub true X (fun i => negb (X i)) false (fun _ => false) (fun _ => false) (fun _ => false)).
  apply (Huniv x_star (C_p5_x_star r q s) T); [|reflexivity].
  split.
  - split.
    + intros w HwC [Wd [WA [WB _]]]. rewrite kappa_p5_x_star.
      unfold kappa_p5. rewrite (Wd eq_refl). simpl.
      unfold x_ok. apply forall_nat_true. intros i Hi.
      destruct (X i) eqn:EX; [rewrite (WA i Hi EX); reflexivity | rewrite (WB i Hi); [apply Bool.orb_true_r | simpl; rewrite EX; reflexivity]].
    + intros S' Hlt Hw'.
      destruct Hlt as [[H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]] Hdiff].
      destruct Hdiff as [[Hd1 Hd0] | [[i0 [Hi0 [HA1 HA0]]] | [[i0 [Hi0 [HB1 HB0]]] | [[Hp1 Hp0] |
                       [[j0 [Hj0 [HY1 HY0]]] | [[j0 [Hj0 [HYb1 HYb0]]] | [k0 [Hk0 [HZ1 HZ0]]]]]]]]];
      simpl in *; try discriminate.
      * pose proof (Hw' inst_dummy (C_p5_dummy r q s)) as Hkd.
        rewrite kappa_p5_dummy, kappa_p5_x_star in Hkd. symmetry in Hkd.
        assert (Habs : true = false).
        { apply Hkd. repeat split; unfold inst_dummy, x_star; simpl; intros;
          first [ reflexivity
                | congruence
                | exfalso; apply Bool.diff_true_false; symmetry;
                  first [ apply H4; assumption
                        | eapply H5; eassumption
                        | eapply H6; eassumption
                        | eapply H7; eassumption ] ]. }
        discriminate.
      * set (w := mkInst true (fun i => if i =? i0 then false else true)
                              (fun i => if i =? i0 then false else true)
                              true (fun _ => true) (fun _ => true) (fun _ => true)).
        assert (HwC : C_p5 r q s w = true).
        { unfold C_p5, w, all_Y_true. simpl.
          match goal with |- _ && (if ?c then true else true) = true => destruct c; rewrite Bool.andb_true_r; apply forall_nat_true; intros; reflexivity end. }
        pose proof (Hw' w HwC) as Hkw.
        assert (Hwag : agrees_on r q s w x_star S').
        { repeat split; unfold w; simpl; intros; try reflexivity;
          destruct (Nat.eqb_spec i i0); try reflexivity; subst; exfalso;
          first [ congruence
                | pose proof (H2 i0 Hi0 H0); destruct (X i0); simpl in *; congruence
                | pose proof (H3 i0 Hi0 H0); destruct (X i0); simpl in *; congruence ]. }
        specialize (Hkw Hwag). rewrite kappa_p5_x_star in Hkw.
        unfold kappa_p5, w, x_ok in Hkw. simpl in Hkw.
        pose proof (forall_nat_elim r _ Hkw i0 Hi0) as H0. simpl in H0. rewrite Nat.eqb_refl in H0. discriminate.
      * set (w := mkInst true (fun i => if i =? i0 then false else true)
                              (fun i => if i =? i0 then false else true)
                              true (fun _ => true) (fun _ => true) (fun _ => true)).
        assert (HwC : C_p5 r q s w = true).
        { unfold C_p5, w, all_Y_true. simpl.
          match goal with |- _ && (if ?c then true else true) = true => destruct c; rewrite Bool.andb_true_r; apply forall_nat_true; intros; reflexivity end. }
        pose proof (Hw' w HwC) as Hkw.
        assert (Hwag : agrees_on r q s w x_star S').
        { repeat split; unfold w; simpl; intros; try reflexivity;
          destruct (Nat.eqb_spec i i0); try reflexivity; subst; exfalso;
          first [ congruence
                | pose proof (H2 i0 Hi0 H0); destruct (X i0); simpl in *; congruence
                | pose proof (H3 i0 Hi0 H0); destruct (X i0); simpl in *; congruence ]. }
        specialize (Hkw Hwag). rewrite kappa_p5_x_star in Hkw.
        unfold kappa_p5, w, x_ok in Hkw. simpl in Hkw.
        pose proof (forall_nat_elim r _ Hkw i0 Hi0) as H0. simpl in H0. rewrite Nat.eqb_refl in H0. discriminate.
  - intros S [HS _] [Hcov [v [HvC [HvT HvnS]]]].
    assert (HSsub : forall i, i < r -> (sXp S i = true -> X i = true) /\ (sXm S i = true -> X i = false)).
    { intros i Hi. split; intro Hs.
      - destruct (X i) eqn:EX; [reflexivity|].
        set (u := mkInst true (fun k => if k =? i then false else true) (fun _ => true) true (fun _ => true) (fun _ => true) (fun _ => true)).
        assert (HuC : C_p5 r q s u = true).
        { unfold C_p5, u, all_Y_true. simpl.
          match goal with |- _ && (if ?c then true else true) = true => destruct c; rewrite Bool.andb_true_r; apply forall_nat_true; intros; reflexivity end. }
        assert (HuT : agrees_on r q s u x_star T).
        { repeat split; unfold u, T; simpl; intros; try discriminate; try reflexivity.
          destruct (Nat.eqb_spec i0 i); [subst; rewrite EX in H0; discriminate | reflexivity]. }
        destruct (Hcov u HuC HuT) as [_ [uA _]]. specialize (uA i Hi Hs). unfold u in uA; simpl in uA; rewrite Nat.eqb_refl in uA; discriminate.
      - destruct (X i) eqn:EX; [|reflexivity].
        set (u := mkInst true (fun _ => true) (fun k => if k =? i then false else true) true (fun _ => true) (fun _ => true) (fun _ => true)).
        assert (HuC : C_p5 r q s u = true).
        { unfold C_p5, u, all_Y_true. simpl.
          match goal with |- _ && (if ?c then true else true) = true => destruct c; rewrite Bool.andb_true_r; apply forall_nat_true; intros; reflexivity end. }
        assert (HuT : agrees_on r q s u x_star T).
        { repeat split; unfold u, T; simpl; intros; try discriminate; try reflexivity.
          destruct (Nat.eqb_spec i0 i); [subst; rewrite EX in H0; discriminate | reflexivity]. }
        destruct (Hcov u HuC HuT) as [_ [_ [uB _]]]. specialize (uB i Hi Hs). unfold u in uB; simpl in uB; rewrite Nat.eqb_refl in uB; discriminate. }
    assert (HSZ : forall k, k < s -> sZ S k = false).
    { intros k Hk. destruct (sZ S k) eqn:EZ; [|reflexivity].
      set (u := mkInst true (fun _ => true) (fun _ => true) true (fun _ => true) (fun _ => true) (fun m => negb (m =? k))).
      assert (HuC : C_p5 r q s u = true).
      { unfold C_p5, u, all_Y_true. simpl.
        match goal with |- _ && (if ?c then true else true) = true => destruct c; rewrite Bool.andb_true_r; apply forall_nat_true; intros; reflexivity end. }
      assert (HuT : agrees_on r q s u x_star T).
      { repeat split; unfold u, T; simpl; intros; try discriminate; try reflexivity. }
      destruct (Hcov u HuC HuT) as [_ [_ [_ [_ [_ [_ uZ]]]]]]. specialize (uZ k Hk EZ). unfold u in uZ; simpl in uZ; rewrite Nat.eqb_refl in uZ; discriminate. }
    destruct (sd S) eqn:ESd.
    + (* If sd S = true, S must fix A_i or B_i for all i < r, so cov_S <= cov_T, contradicting v *)
      assert (HSAB : forall i, i < r -> sXp S i = true \/ sXm S i = true).
      { intros i Hi. destruct (sXp S i) eqn:EA; [left; reflexivity|]. destruct (sXm S i) eqn:EB; [right; reflexivity|].
        exfalso.
        set (w := mkInst true (fun k => if k =? i then false else true) (fun k => if k =? i then false else true)
                              true (fun _ => true) (fun _ => true) (fun _ => true)).
        assert (HwC : C_p5 r q s w = true).
        { unfold C_p5, w, all_Y_true. simpl.
          match goal with |- _ && (if ?c then true else true) = true => destruct c; rewrite Bool.andb_true_r; apply forall_nat_true; intros; reflexivity end. }
        assert (HwS : agrees_on r q s w x_star S).
        { repeat split; unfold w; simpl; intros; try reflexivity.
          - destruct (Nat.eqb_spec i0 i); [subst; rewrite EA in H0; discriminate | reflexivity].
          - destruct (Nat.eqb_spec i0 i); [subst; rewrite EB in H0; discriminate | reflexivity]. }
        pose proof (HS w HwC HwS) as Hkw. rewrite kappa_p5_x_star in Hkw.
        unfold kappa_p5, w, x_ok in Hkw. simpl in Hkw.
        pose proof (forall_nat_elim r _ Hkw i Hi) as H0. simpl in H0. rewrite Nat.eqb_refl in H0. discriminate. }
      apply HvnS. destruct HvT as [vD [vA [vB _]]].
      assert (Hvd : fd v = true) by (apply vD; exact ESd).      assert (HvA : forall i, i < r -> X i = true -> fXp v i = true).
      { intros i Hi EX. destruct (HSAB i Hi) as [EA|EB];
        [ rewrite (vA i Hi EA); reflexivity | rewrite (proj2 (HSsub i Hi) EB) in EX; discriminate ]. }
      assert (HvB : forall i, i < r -> X i = false -> fXm v i = true).
      { intros i Hi EX. destruct (HSAB i Hi) as [EA|EB];
        [ rewrite (proj1 (HSsub i Hi) EA) in EX; discriminate | rewrite (vB i Hi EB); reflexivity ]. }
      repeat split; simpl; intros; try discriminate.
      * exact Hvd.
      * exact (HvA i H H0).
      * destruct (X i) eqn:EX; [discriminate | exact (HvB i H EX)].
    + (* sd S = false: check if any j < q has both sYp S j = true /\ sYm S j = true *)
      destruct (classic (exists j, j < q /\ sYp S j = true /\ sYm S j = true)) as [[j0 [Hj0 [HY1 HYb1]]] | HnotYboth].
      * assert (HSd1 : forall w, C_p5 r q s w = true -> agrees_on r q s w x_star S -> fd w = true).
        { intros w HwC [_ [_ [_ [_ [WY [WYb _]]]]]].
          destruct (fd w) eqn:Ewd; [reflexivity|]. exfalso.
          unfold C_p5 in HwC. rewrite Ewd in HwC.
          destruct (fp w).
          - apply Bool.andb_true_iff in HwC. destruct HwC as [_ Hwyn]. unfold y_not11 in Hwyn.
            pose proof (forall_nat_elim q _ Hwyn j0 Hj0) as H0. simpl in H0.
            rewrite (WY j0 Hj0 HY1), (WYb j0 Hj0 HYb1) in H0. discriminate.
          - unfold dummy_body in HwC. apply Bool.andb_true_iff in HwC. destruct HwC as [Hw1 _].
            apply Bool.andb_true_iff in Hw1. destruct Hw1 as [_ HwY].
            pose proof (forall_nat_elim q _ HwY j0 Hj0) as H0. simpl in H0.
            rewrite (WY j0 Hj0 HY1) in H0. discriminate. }
        assert (HSAB : forall i, i < r -> sXp S i = true \/ sXm S i = true).
        { intros i Hi. destruct (sXp S i) eqn:EA; [left; reflexivity|]. destruct (sXm S i) eqn:EB; [right; reflexivity|].
          exfalso.
          set (w := mkInst true (fun k => if k =? i then false else true) (fun k => if k =? i then false else true)
                                true (fun _ => true) (fun _ => true) (fun _ => true)).
          assert (HwC : C_p5 r q s w = true).
          { unfold C_p5, w, all_Y_true. simpl.
            match goal with |- _ && (if ?c then true else true) = true => destruct c; rewrite Bool.andb_true_r; apply forall_nat_true; intros; reflexivity end. }
          assert (HwS : agrees_on r q s w x_star S).
          { repeat split; unfold w; simpl; intros; try reflexivity; try (rewrite ESd in *; discriminate).
            - destruct (Nat.eqb_spec i0 i); [subst; rewrite EA in H0; discriminate | reflexivity].
            - destruct (Nat.eqb_spec i0 i); [subst; rewrite EB in H0; discriminate | reflexivity]. }
          pose proof (HS w HwC HwS) as Hkw. rewrite kappa_p5_x_star in Hkw.
          unfold kappa_p5, w, x_ok in Hkw. simpl in Hkw.
          pose proof (forall_nat_elim r _ Hkw i Hi) as H0. simpl in H0. rewrite Nat.eqb_refl in H0. discriminate. }
        apply HvnS. pose proof (HSd1 v HvC HvT) as Hvd. destruct HvT as [vD [vA [vB _]]].      assert (HvA : forall i, i < r -> X i = true -> fXp v i = true).
      { intros i Hi EX. destruct (HSAB i Hi) as [EA|EB];
        [ rewrite (vA i Hi EA); reflexivity | rewrite (proj2 (HSsub i Hi) EB) in EX; discriminate ]. }
      assert (HvB : forall i, i < r -> X i = false -> fXm v i = true).
      { intros i Hi EX. destruct (HSAB i Hi) as [EA|EB];
        [ rewrite (proj1 (HSsub i Hi) EA) in EX; discriminate | rewrite (vB i Hi EB); reflexivity ]. }
      repeat split; simpl; intros; try discriminate.
        -- exact Hvd.
        -- exact (HvA i H H0).
        -- destruct (X i) eqn:EX; [discriminate | exact (HvB i H EX)].
      * set (Y := fun j => negb (sYm S j)).
        destruct (HX Y) as [Z HZ].
        set (w := inst_d0_p1 X Y Z).
        assert (HwC : C_p5 r q s w = true) by apply C_p5_d0_p1.
        assert (HwS : agrees_on r q s w x_star S).
        { repeat split; unfold w; simpl; intros; try reflexivity.
          - rewrite ESd in H; discriminate.
          - rewrite (proj1 (HSsub i H) H0). reflexivity.
          - rewrite (proj2 (HSsub i H) H0). reflexivity.
          - unfold Y. destruct (sYm S j) eqn:EYb; [exfalso; apply HnotYboth; exists j; auto | reflexivity].
          - unfold Y. rewrite H0. reflexivity.
          - rewrite HSZ in H0; [discriminate | exact H]. }
        pose proof (HS w HwC HwS) as Hkw.
        unfold w in Hkw. rewrite kappa_p5_x_star, kappa_p5_d0_p1, HZ in Hkw. discriminate.
Qed.

(* ========================================================================= *)
(* Main Equivalence Theorem: P5 is Pi_3^P-complete                           *)
(* ========================================================================= *)

Theorem p5_pi3p_equiv : forall r q s phi,
  1 <= r -> 1 <= q ->
  cnf_bounded (r + q + s) phi ->
  (cls_univ_fair r q s phi <-> ~ three_qbf r q phi).
Proof.
  intros r q s phi Hr Hq Hbnd. split.
  - intro Hfair. intro Hqbf. exact (three_qbf_implies_not_cls_univ_fair r q s phi Hqbf Hfair).
  - exact (neg_three_qbf_implies_cls_univ_fair r q s phi Hr Hq Hbnd).
Qed.

Print Assumptions p5_constrained_ftu.
Print Assumptions p5_pi3p_equiv.

