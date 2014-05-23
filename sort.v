(** Podpora za algoritme za urejanje. *)

(** Delali bomo s seznami celih števil, pri čemer bomo uporabljali
    cela števila iz knjižnice [ZArith]. To so binarna cela števila,
    s katerimi lahko "učinkovito" računamo. *)

Require Import List.
Require Import Bool.
Require Import ZArith.

(** Aktiviramo notacijo za sezname. *)
Local Open Scope list_scope.

(** Najprej je treba definirati pojma "seznam je urejen" in
    "seznam [l1] je permutacija seznama [l2]". 

    Izkaže se, da je "permutacija" tehnično precej zahtevna.
    Omejili se bomo na "seznama [l1] in [l2] imata enake elemente".
    Seznama [1;1;2] in [1;2;2] imata enake elemente in sta
    enako dolga, a nista permutacija drug drugega.
*)

(** Seznam je urejen, če je prazen, ima en element, ali je
    oblike [x :: y :: _], kjer je [x <= y] in je rep
    [y :: _] urejen. 

    Uporabili bomo vzorec [(y :: _) as l'], ki pomeni "seznam
    [l'] oblike [y :: _]". S tem hkrati dobimo prvi element
    seznama [y] in celoten seznam [l'].
*)
Fixpoint urejen (l : list Z) :=
  match l with
    | nil => True
    | _ :: nil => True
    | x :: ((y :: _) as l') => (x <= y)%Z /\ urejen l'
  end.

(** Relacija [In x l] pomeni, da je [x] element seznama [l]. *)

Fixpoint vsebuje (l1 l2 : list Z) :=
  match l1 with
    | nil => True
    | x :: l => In x l2 /\ vsebuje l l2
  end.

Lemma vsebuje_In (x : Z) (l1 l2 : list Z) :
  In x l1 -> vsebuje l1 l2 -> In x l2.
Proof.
  admit. (* To bo naredil Jernej. *)
Qed.

(** Seznama [l1] in [l2] imata enake elemente, če sta
    vsebovana drug v drugem. *)
Definition enak (l1 l2 : list Z) :=
  vsebuje l1 l2 /\ vsebuje l2 l1.

(** Osnovne leme o vsebovanosti. *)

Lemma vsebuje_cons (x : Z) (l1 l2 : list Z) :
  vsebuje l1 l2 -> vsebuje l1 (x :: l2).
Proof.
  admit. (* To bo naredil Stepišnik. *)
Qed.

Lemma vsebuje_refl (l : list Z) : vsebuje l l.
Proof.
  induction l.
  - simpl ; auto.
  - simpl.
    split ; auto.
    now apply vsebuje_cons.
Qed.

Lemma vsebuje_trans (l1 l2 l3 : list Z) :
  vsebuje l1 l2 -> vsebuje l2 l3 -> vsebuje l1 l3.
Proof.
  admit. (* To bo naredila Eva. *)
Qed.
    
(** Vsak seznam je enak sam sebi. *)
Lemma enak_refl (l : list Z) : enak l l.
Proof.
  split ; apply vsebuje_refl.
Qed.

(** Če staknemo enake sezname, dobimo enaka seznama. *)

Lemma vsebuje_app (l1 l1' l2 l2' : list Z) :
  vsebuje l1 l1' -> vsebuje l2 l2' -> vsebuje (l1 ++ l2) (l1' ++ l2').
Proof.
  admit. (* To bo naredil Janoš. *)
Qed.

Lemma enak_app (l1 l1' l2 l2' : list Z) :
  enak l1 l1' -> enak l2 l2' -> enak (l1 ++ l2) (l1' ++ l2').
Proof.
  intros [H1 G1] [H2 G2].
  split ; now apply vsebuje_app.
Qed.
    
(** Če enakima seznamoma dodamo element na začetku, dobimo
    enaka seznama. *)
Lemma enak_cons (x : Z) (l1 l2 : list Z) :
  enak l1 l2 -> enak (x :: l1) (x :: l2).
Proof.
  intros [H1 H2].
  split ; simpl ; auto using vsebuje_cons.
Qed.

(** Potrebovali bomo tudi operacije, ki sezname razdelijo na dva
    podseznama. Na primer, v urejanju z zlivanjem seznam razdelimo
    takole: *)

Fixpoint razpolovi (l : list Z) :=
  match l with
    | nil => (nil, nil)
    | x :: nil => (nil, x :: nil)
    | x :: y :: l' =>
      let (l1, l2) := razpolovi l' in
        (x :: l1, y :: l2)
  end.

Eval compute in (razpolovi (1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: 8 :: 9 :: nil)%Z).

(** To je pomožna oblika indukcije na seznamih. Pravi, pa tole:
    denimo, da lastnost P in da

    - nil ima lastnost P
    - seznam z enim elementom (x :: nil) ima lastnost P, za vsak x
    - če ima seznam l lastnost P, potem ima tudi x :: y :: l lastnost P, za vse x, y, l

    Tedaj ima vsak seznam lasnost P.

    To inačico indukcije najlažje dokažemo tako, da napišemo ustrezno
    rekurzivno funkcijo, ki je po Curry-Howardu njen dokaz.
*)
Fixpoint list_ind_2
         {A : Set}
         (P : list A -> Prop)
         (p0 : P nil)
         (p1 : forall x, P (x :: nil))
         (p2 : forall x y l, P l -> P (x :: y :: l))
         (l : list A) :=
  match l return P l with
    | nil => p0
    | x :: nil => p1 x
    | x :: y :: l' => p2 x y l' (list_ind_2 P p0 p1 p2 l')
  end.

(** Osnovne lastnosti razpolavljanja. *)

Lemma razpolovi_length (l : list Z) :
  let (l1, l2) := razpolovi l in
  length l = length l1 + length l2.
Proof.
  apply (list_ind_2 (fun l =>
                            let (l1, l2) := razpolovi l in
                            length l = length l1 + length l2)).
  - simpl ; auto.
  - simpl ; auto.
  - intros x y l' H.
    simpl.
    replace (razpolovi l') with (fst (razpolovi l'), snd (razpolovi l')) in * |- * ;
      [ idtac | symmetry ; apply surjective_pairing ].
    simpl.
    rewrite <- plus_n_Sm.
    now repeat f_equal.
Qed.

(** Nekateri algoritmi za urejanje razdelijo seznam na podseznama
    glede na dani kriterij [p]. *)
Fixpoint razdeli (p : Z -> bool) (l : list Z) :=
  match l with
    | nil => (nil, nil)
    | x :: l' =>
      let (l1, l2) := razdeli p l' in
        if p x then (x :: l1, l2) else (l1, x :: l2)
  end.

(** Na primer, takole razdelimo dani seznam glede na to,
    ali so elementi večji od 5. *)
Eval compute in (razdeli (Z.leb 5) (10 :: 1 :: 1 :: 3 :: 8 :: 7 :: 5 :: nil)%Z).
 
Lemma razdeli_length (p : Z -> bool) (l : list Z) :
  let (l1, l2) := razdeli p l in
    length l = length l1 + length l2.
Proof.
  induction l.
  - simpl ; auto.
  - simpl.
    replace (razdeli p l) with (fst (razdeli p l), snd (razdeli p l)) in * |- * ;
      [ idtac | symmetry ; apply surjective_pairing ].
    destruct (p a) ; simpl.
    + now f_equal.
    + rewrite <- plus_n_Sm.
      now f_equal.
Qed.

(** Nekateri algoritmi izračunajo minimalni element seznama. 
    Ker minimalni element praznega seznama ne obstaja, vedno
    računamo minimalni element sestavljenega seznama [x :: l].
*)
Fixpoint najmanjsi (x : Z) (l : list Z) : Z :=
  match l with
    | nil => x
    | y :: l' =>
      if Z.leb x y then najmanjsi x l' else najmanjsi y l'
  end.

Eval compute in (najmanjsi 4 (10 :: 1 :: 1 :: 3 :: 8 :: 7 :: 5 :: nil)%Z).

(** Osnovne lemen o najmanjsinih elementih. *)

Lemma najmanjsi_inv (x : Z) (l : list Z) :
  x = najmanjsi x l \/ In (najmanjsi x l) l.
Proof.
  generalize x.
  induction l ; auto.
  intro y.
  simpl; destruct (Z.leb y a).
  - destruct (IHl y) ; auto.
  - destruct (IHl a) ; auto.
Qed. 

Lemma najmanjsi_In (x : Z) (l : list Z) : 
  In (najmanjsi x l) (x :: l).
Proof.
  destruct (najmanjsi_inv x l).
  - rewrite <- H ; simpl ; auto.
  - simpl ; auto.
Qed.

Lemma najmanjsi_head (x : Z) (l : list Z) :
  (najmanjsi x l <= x)%Z.
Proof.
  generalize x.
  induction l.
  - intro ; reflexivity.
  - intro y ; simpl.
    case_eq (Z.leb y a) ; intro E.
    + apply IHl.
    + transitivity a ; [apply IHl | idtac].
      admit.
Qed.

Lemma najmanjsi_tail x y l : In y l -> (najmanjsi x l <= y)%Z.
Proof.
  generalize x y ; clear x y.
  induction l ; [intros ? ? H ; destruct H | idtac].
  intros x y H.
  apply in_inv in H ; destruct H as [G|G] ; admit.
Qed.

Lemma najmanjsi_spodna_meja (x : Z) (l : list Z) :
  forall y, In y (x :: l) -> (najmanjsi x l <= y)%Z.
Proof.
  intros y [H|H].
  - rewrite H ; apply najmanjsi_head.
  - now apply najmanjsi_tail.
Qed. 
