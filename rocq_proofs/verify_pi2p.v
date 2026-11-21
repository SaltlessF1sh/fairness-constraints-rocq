From Stdlib Require Import Bool List Arith Lia.
Import ListNotations.

(* ========================================================================= *)
(* Constructive Formal Verification in Rocq (Coq)                            *)
(*   1. ~ two_qbf r phi <-> is_loose r s (C_red r phi)                       *)
(*   2. ~ two_qbf r phi <-> is_disentangled r s (C_red r phi) kappa_d (r>=1) *)
(* Establishing Pi_2^P-completeness of Looseness (Definition 22) and         *)
(* Disentangledness (Definition 25) in Cooper & Bousdira (CP 2026).          *)
(* ========================================================================= *)

Definition lit := (nat * bool)%type.
Definition term := list lit.
Definition dnf := list term.

Definition eval_lit (assign : nat -> bool) (l : lit) : bool :=
  Bool.eqb (assign (fst l)) (snd l).

Fixpoint eval_term (assign : nat -> bool) (t : term) : bool :=
  match t with
  | [] => true
  | l :: rest => eval_lit assign l && eval_term assign rest
  end.

Fixpoint eval_dnf (assign : nat -> bool) (phi : dnf) : bool :=
  match phi with
  | [] => false
  | t :: rest => eval_term assign t || eval_dnf assign rest
  end.

Definition dnf_bounded (n : nat) (phi : dnf) : Prop :=
  forall t, In t phi -> forall l, In l t -> fst l < n.

Lemma eval_dnf_ext : forall phi f g,
  (forall k, f k = g k) ->
  eval_dnf f phi = eval_dnf g phi.
Proof.
  intros phi f g Hext.
  induction phi as [|t rest IH]; simpl; [reflexivity|].
  f_equal; [|apply IH].
  induction t as [|l ts IHt]; simpl; [reflexivity|].
  f_equal; [unfold eval_lit; rewrite Hext; reflexivity | apply IHt].
Qed.

Definition combine_XZ (r : nat) (X Z : nat -> bool) (k : nat) : bool :=
  if k <? r then X k else Z (k - r).

(* Existential-Universal 2-QBF: exists X, forall Z, Phi(X, Z) = true
   Negation (~ two_qbf r phi) is forall X, exists Z, ~Phi(X, Z) (CNF), i.e., Pi_2^P-complete *)
Definition two_qbf (r : nat) (phi : dnf) : Prop :=
  exists X : nat -> bool, forall Z : nat -> bool,
    eval_dnf (combine_XZ r X Z) phi = true.

Record Instance := mkInst {
  inst_d : bool;
  inst_X : nat -> bool;
  inst_pstar : bool;
  inst_Z : nat -> bool
}.

(* Protected feature: None = p_star, Some j = Z_j (with j < s) *)
Definition ProtFeat := option nat.

Definition prot_bounded (s : nat) (p : ProtFeat) : Prop :=
  match p with
  | None => True
  | Some j => j < s
  end.

Definition agree_N (r : nat) (x y : Instance) : Prop :=
  inst_d x = inst_d y /\ forall i, i < r -> inst_X x i = inst_X y i.

Definition get_P (x : Instance) (p : ProtFeat) : bool :=
  match p with
  | None => inst_pstar x
  | Some j => inst_Z x j
  end.

Definition p_strictly_subsumes_N (r : nat) (C : Instance -> bool) (x : Instance) (p : ProtFeat) : Prop :=
  (forall z : Instance, C z = true -> agree_N r z x -> get_P z p = get_P x p) /\
  (exists y : Instance, C y = true /\ get_P y p = get_P x p /\ ~ agree_N r y x).

(* Definition 22: Looseness (over finite protected features P = {p^*, Z_0..Z_{s-1}}) *)
Definition is_loose (r s : nat) (C : Instance -> bool) : Prop :=
  forall x : Instance, C x = true ->
    forall p : ProtFeat, prot_bounded s p -> ~ p_strictly_subsumes_N r C x p.

Record Subset := mkSub {
  sub_d : bool;
  sub_X : nat -> bool;
  sub_pstar : bool;
  sub_Z : nat -> bool
}.

Definition is_unfair_sub (s : nat) (Q : Subset) : Prop :=
  sub_pstar Q = true \/ exists j : nat, j < s /\ sub_Z Q j = true.

Definition agree_sub (r s : nat) (Q : Subset) (x y : Instance) : Prop :=
  (sub_d Q = true -> inst_d x = inst_d y) /\
  (forall i, i < r -> sub_X Q i = true -> inst_X x i = inst_X y i) /\
  (sub_pstar Q = true -> inst_pstar x = inst_pstar y) /\
  (forall j, j < s -> sub_Z Q j = true -> inst_Z x j = inst_Z y j).

Definition weak_axp_sub (r s : nat) (C kappa : Instance -> bool) (Q : Subset) (x : Instance) : Prop :=
  forall y : Instance, C y = true -> agree_sub r s Q x y -> kappa y = kappa x.

Definition weak_axp_N (r : nat) (C kappa : Instance -> bool) (x : Instance) : Prop :=
  forall y : Instance, C y = true -> agree_N r x y -> kappa y = kappa x.

Definition Q_strictly_subsumes_N (r s : nat) (C : Instance -> bool) (Q : Subset) (x : Instance) : Prop :=
  (forall z : Instance, C z = true -> agree_N r z x -> agree_sub r s Q x z) /\
  (exists y : Instance, C y = true /\ agree_sub r s Q x y /\ ~ agree_N r y x).

(* Definition 25: Disentangledness *)
Definition is_disentangled (r s : nat) (C kappa : Instance -> bool) : Prop :=
  forall x : Instance, C x = true ->
    weak_axp_N r C kappa x /\
    forall Q : Subset, is_unfair_sub s Q -> weak_axp_sub r s C kappa Q x ->
      ~ Q_strictly_subsumes_N r s C Q x.

(* Reduction construction *)
Definition C_red (r : nat) (phi : dnf) (x : Instance) : bool :=
  negb (inst_d x) || inst_pstar x || negb (eval_dnf (combine_XZ r (inst_X x) (inst_Z x)) phi).

Definition kappa_d (x : Instance) : bool := inst_d x.

Lemma C_red_d_false : forall r phi X p Z,
  C_red r phi (mkInst false X p Z) = true.
Proof. intros. unfold C_red. simpl. reflexivity. Qed.

Lemma C_red_p_true : forall r phi d X Z,
  C_red r phi (mkInst d X true Z) = true.
Proof. intros. unfold C_red. simpl. rewrite Bool.orb_true_r. reflexivity. Qed.

(* Helper: witness flipping Z_j while keeping d, X, pstar=true *)
Definition flip_Z (Z : nat -> bool) (j : nat) (k : nat) : bool :=
  if k =? j then negb (Z j) else Z k.

Theorem looseness_pi2p_equiv :
  forall (r s : nat) (phi : dnf),
    dnf_bounded (r + s) phi ->
    (~ two_qbf r phi <-> is_loose r s (C_red r phi)).
Proof.
  intros r s phi Hbnd. split.
  - (* ~ two_qbf -> is_loose *)
    intros Hnot x HCx p Hp [Hsub _].
    destruct (inst_d x) eqn:Hdx.
    + destruct p as [j |].
      * (* Case p = Some j (Z_j) *)
        set (z := mkInst true (inst_X x) true (flip_Z (inst_Z x) j)).
        assert (HCz : C_red r phi z = true) by apply C_red_p_true.
        assert (Hag : agree_N r z x) by (split; [simpl; congruence | intros i _; reflexivity]).
        specialize (Hsub z HCz Hag).
        unfold get_P, z, flip_Z in Hsub. simpl in Hsub.
        rewrite Nat.eqb_refl in Hsub.
        destruct (inst_Z x j); discriminate.
      * (* Case p = None (p_star) *)
        destruct (inst_pstar x) eqn:Hpx.
        -- apply Hnot. exists (inst_X x). intro Z.
           destruct (eval_dnf (combine_XZ r (inst_X x) Z) phi) eqn:Hev; [reflexivity|].
           exfalso.
           set (z := mkInst true (inst_X x) false Z).
           assert (HCz : C_red r phi z = true).
           { unfold C_red, z. simpl. rewrite Hev. reflexivity. }
           assert (Hag : agree_N r z x) by (split; [simpl; congruence | intros i _; reflexivity]).
           specialize (Hsub z HCz Hag).
           unfold get_P, z in Hsub. simpl in Hsub. rewrite Hpx in Hsub. discriminate.
        -- set (z := mkInst true (inst_X x) true (inst_Z x)).
           assert (HCz : C_red r phi z = true) by apply C_red_p_true.
           assert (Hag : agree_N r z x) by (split; [simpl; congruence | intros i _; reflexivity]).
           specialize (Hsub z HCz Hag).
           unfold get_P, z in Hsub. simpl in Hsub. rewrite Hpx in Hsub. discriminate.
    + (* Case inst_d x = false -> all P are free *)
      set (z := mkInst false (inst_X x) (negb (inst_pstar x)) (flip_Z (inst_Z x) (match p with Some j => j | None => 0 end))).
      assert (HCz : C_red r phi z = true) by apply C_red_d_false.
      assert (Hag : agree_N r z x) by (split; [simpl; congruence | intros i _; reflexivity]).
      specialize (Hsub z HCz Hag).
      destruct p as [j |]; unfold get_P, z, flip_Z in Hsub; simpl in Hsub.
      * rewrite Nat.eqb_refl in Hsub. destruct (inst_Z x j); discriminate.
      * destruct (inst_pstar x); discriminate.
  - (* is_loose -> ~ two_qbf *)
    intros Hloose [X HX].
    set (x := mkInst true X true (fun _ => false)).
    assert (HCx : C_red r phi x = true) by apply C_red_p_true.
    apply (Hloose x HCx None I). split.
    + intros z HCz [Hzd HzX].
      unfold get_P, x. simpl.
      destruct (inst_pstar z) eqn:Hpz; [reflexivity|].
      exfalso. unfold C_red in HCz. rewrite Hzd, Hpz in HCz. simpl in HCz.
      assert (Heq : eval_dnf (combine_XZ r (inst_X z) (inst_Z z)) phi =
                    eval_dnf (combine_XZ r X (inst_Z z)) phi).
      { apply eval_dnf_ext. intro k. unfold combine_XZ.
        destruct (Nat.ltb_spec k r) as [Hk|Hk]; [apply HzX; exact Hk | reflexivity]. }
      rewrite Heq, (HX (inst_Z z)) in HCz. discriminate.
    + exists (mkInst false X true (fun _ => false)).
      split; [apply C_red_d_false|].
      split; [reflexivity|].
      intros [Hc _]. simpl in Hc. discriminate.
Qed.

(* ========================================================================= *)
(* Main Theorem 2: For r >= 1, ~ two_qbf r phi <-> is_disentangled with      *)
(* the non-trivial classifier kappa_d(x) = inst_d x.                         *)
(* ========================================================================= *)

Definition flip_X0 (X : nat -> bool) (i : nat) : bool :=
  if i =? 0 then negb (X 0) else X i.

Theorem disentangled_pi2p_equiv :
  forall (r s : nat) (phi : dnf),
    r >= 1 ->
    dnf_bounded (r + s) phi ->
    (~ two_qbf r phi <-> is_disentangled r s (C_red r phi) kappa_d).
Proof.
  intros r s phi Hr Hbnd. split.
  - (* ~ two_qbf -> is_disentangled *)
    intros Hnot x HCx. split.
    + (* weak_axp_N *)
      intros y HCy [Hyd _]. unfold kappa_d. congruence.
    + (* no unfair Q strictly subsumes N *)
      intros Q Hunfair Haxp [HQsub [y [HCy [HQag Hyneq]]]].
      destruct Hunfair as [Hpstar | [j [Hjs HZj]]].
      * (* p = None (pstar) *)
        apply (proj1 (looseness_pi2p_equiv r s phi Hbnd) Hnot x HCx None I).
        split.
        -- intros z HCz HzN. specialize (HQsub z HCz HzN).
           destruct HQsub as [_ [_ [Hp _]]]. symmetry. exact (Hp Hpstar).
        -- exists y. repeat split; [exact HCy | | exact Hyneq].
           destruct HQag as [_ [_ [Hp _]]]. symmetry. exact (Hp Hpstar).
      * (* p = Some j (Z_j) with j < s *)
        apply (proj1 (looseness_pi2p_equiv r s phi Hbnd) Hnot x HCx (Some j) Hjs).
        split.
        -- intros z HCz HzN. specialize (HQsub z HCz HzN).
           destruct HQsub as [_ [_ [_ HZ]]]. symmetry. exact (HZ j Hjs HZj).
        -- exists y. repeat split; [exact HCy | | exact Hyneq].
           destruct HQag as [_ [_ [_ HZ]]]. symmetry. exact (HZ j Hjs HZj).
  - (* is_disentangled -> ~ two_qbf *)
    intros Hdis [X HX].
    set (x := mkInst true X true (fun _ => false)).
    assert (HCx : C_red r phi x = true) by apply C_red_p_true.
    destruct (Hdis x HCx) as [_ HnoQ].
    set (Q := mkSub true (fun _ => false) true (fun _ => false)).
    apply (HnoQ Q).
    + left. reflexivity.
    + intros y HCy [Hyd _]. unfold kappa_d. symmetry. apply Hyd. reflexivity.
    + split.
      * intros z HCz [Hzd HzX].
        split; [intro; simpl in Hzd; symmetry; exact Hzd |].
        split; [intros i _ Hdisc; simpl in Hdisc; discriminate |].
        split; [intro; unfold x; simpl;
          destruct (inst_pstar z) eqn:Hpz; [reflexivity|];
          exfalso; unfold C_red in HCz; rewrite Hzd, Hpz in HCz; simpl in HCz;
          assert (Heq : eval_dnf (combine_XZ r (inst_X z) (inst_Z z)) phi =
                        eval_dnf (combine_XZ r X (inst_Z z)) phi)
            by (apply eval_dnf_ext; intro k; unfold combine_XZ;
                destruct (Nat.ltb_spec k r) as [Hk|Hk]; [apply HzX; exact Hk | reflexivity]);
          rewrite Heq, (HX (inst_Z z)) in HCz; discriminate |].
        intros j _ Hdisc; simpl in Hdisc; discriminate.
      * exists (mkInst true (flip_X0 X) true (fun _ => false)).
        split; [apply C_red_p_true|].
        split.
        -- split; [intro; reflexivity|].
           split; [intros i _ Hdisc; simpl in Hdisc; discriminate|].
           split; [intro; reflexivity|].
           intros j _ Hdisc; simpl in Hdisc; discriminate.
        -- intros [_ HXeq]. specialize (HXeq 0 Hr). simpl in HXeq.
           unfold flip_X0 in HXeq. simpl in HXeq.
           destruct (X 0); discriminate.
Qed.

Print Assumptions looseness_pi2p_equiv.
Print Assumptions disentangled_pi2p_equiv.
