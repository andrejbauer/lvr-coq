(** * Odvisni tipi

    Odvisni tip je preslikava [P : A -> Type]. To je,
    za vsako vrednost [a : A] imamo tip [P a]. Nekaj primerov
    iz prakse:

    - ko v analizi rečemo "odprti interval $(a,b)$" je interval
      _odvisen_ od parametrov $a$ in $b$,

    - ko v računalništvu rečemo "tabela dolžine $n$" je tabela
      _odvisna_ od parametra $n$,

    Skratka, kadarkoli je množica, prostor, ali podatkovni tip
    odvisna od enega ali več parametrov, imamo opravka z odvisnim
    tipom.

    Odvisnemu tipu pravimo tudi _družina tipov_.
*)

(** V Coqu odvisni tip predstavimo kot preslikavo iz tipa parametra
    v [Type]. Tu se ne bomo spuščali v podrobnosti, kaj natančno
    je [Type] -- predstavljamo si ga kot "supertip", ki vsebuje
    vse tipe. (Kaj pa samega sebe?) *)

(** ** Produkti

   Naj bo [P : A -> Type] družina tipov. _Produkt_ družine [P]
   v Coqu zapišemo kot [forall (x : A), P x]. Običajna matematična
   notacija je ∏(x:A) P x. Zakaj pišemo s [forall] bo jasno, ko
   bomo spoznali Curry-Howardov izomorfizem.

   Produktu pravimo tudi _odvisni produkt_.

   Natančneje, če imamo odvisni tip [P : A -> Type], se pravila za
   njegov produkt glasijo:

   - _formacija_: [forall (x : A), P x] tip

   - _vpeljava_: če imamo pri predpostavki [x : A] izraz [e : P x],
     potem je [fun (x : A) => t] izraz tipa [forall (x : A), P x].
     Pravimo mu _odvisna funkcija_.

   - _uporaba_: če je [f : forall (x : A), P x] in [a : A], potem je
     [f a : P a]. Pravimo, da smo [f] aplicirali na [a].

   - _enačbe_:

    - _pravilo $\beta$_: [(fun (x : A) => t) e = t{e/x}] kjer zapis "[t{e/x}]" pomeni,
      da v izrazu [t] vstavimo [e] namesto [x].

    - _pravilo $\eta$_: [(fun (x : A) => f x) = f]

    Kot vidimo, so pravila zelo podobna tistim za funkcijski tip [A -> B]. Pravzaprav je
    [A -> B] le poseben primer produkta. Če namreč definiramo [P : A -> Type] s predpisom
    [P x = B], torej je [P] _konstantna_ družina, tedaj je [forall (x : A), P x] enako
    [forall (x : A), B], ki ima natanko ista pravila kot [A -> B]. V Coqu je [A -> B] v
    resnici definiran kot [forall (x : A), B].  
*)

(** ** Vsota

   Naj bo [P : A -> Type] družina tipov. _Vsoto_ družine [P]
   v Coqu zapišemo kot [{x : A & P x}]. Običajna matematična
   notacija je ∑(x:A) P x. Zapis v Coqu zelo spominja na
   podmnožice. Zakaj je tako, bo jasno, ko bomo spoznali Curry-Howardov
   izomorfizem.

   Vsoti pravimo tudi _odvisna vsota_.

   Natančneje, če imamo odvisni tip [P : A -> Type], se pravila za
   njegovo vsoto glasijo:

   - _formacija_: [{x : A & P x}] je tip

   - _vpeljava_: če je [a : A] in [b : P a], je [existT P a b : {x : A & P x}].
     Izrazu [existT P a b] pravimo _odvisni par_, matematična notacija je $(a,b)$.

   - _uporaba_: če je [p : {x : A & P x}], potem imamo

     - _prva (odvisna) projekcija): [projT1 p : A]
     - _druga (odvisna) projekcija_: [projT2 p : P (projT1 p)]

   - _enačbe_:

     - [projT1 (existT P a b) = a]
     - [projT2 (existT P a b) = b]
     - [existT P (projT1 p) (projT2 p) = p]

   Coq v zadnjo enačbo ne verjame neposredno.

   Pravila za vsoto so zelo podobna tistim za kartezični produkt. In res,
   če je [P : A -> Type] konstantna družina, [P x = B], potem sta [A * B]
   in [{x : A & B}] izomorfna. Zaradi tehničnih razlogov je v Coqu kartezični
   produkt definiran samostojno in ni poseben primer odvisne vsote.
*)

(** Delo s "čistimi" odvisnimi tipi je precej dolgočasno. Bolj zanimivo bo,
    ko bomo spoznali tudi induktivne tipe. Takrat bomo lahko npr. definirali
    odvisni tip "seznam dolžine [n]". V spodnjih vaja se predvsem posvetimo
    Curry-Howardovemu izomorfizmu: produkti so univerzalni kvantifikatorji,
    vsote so eksitenčni kvantifikatorji. *)

Section Vaje1.
  (** Spomnimo se vaje iz predikatnega računa: *)
  Lemma vaja_1 : forall n : nat, exists m : nat, n < m.
  Proof.
    (* predvanja *)
    admit.
  Qed.

  (** Zapišimo jo s tipi. Enak dokaz še vedno deluje. *)
  Lemma vaja1_2 : forall n : nat, { m : nat & n < m }.
  Proof.
    (* predavanja *)
    admit.
  Qed.

  (** Kako bi rešili vajo neposredno, z definicijo funkcije?
      Funkcijo, ki bi jo radi napisali, že imamo in jo dobimo
      s [Print vaja1_2]:

      [fun n : nat => existT (fun m : nat => n < m) (S n) (le_n (S n))]

      Malo verjetno je, da bi kar tako našli [le_n], razen če pogledamo
      definicijo relacije [<=] s [Print le]. Coq omogoča, da funkcijo ali
      katerikoli drug izraz zgradimo deloma, nato pa ga postopoma nadgrajujemo.
      To naredimo s taktiko [refine e], kjer je [e] delno zgrajeni izraz.
      Nedokončane dele označimo s podčrtajem [_].
   *)
  Lemma vaja1_3 : forall n : nat, { m : nat & n < m }.
  Proof.
    (* predavanja *)
    admit.
  Defined.

End Vaje1.

Section Frobenius.
  (** Naslednjo vaje rešimo na več načinov: najprej dokažemo izrek s taktikami,
   nato njegovo verzijo prepiši v tipe in preverimo, ali isti dokaz še vedno
   deluje. Nato še neposredno zapišimo izraz danega tipa, ali uporabimo
   [refine], če je preveč zapleten.

   Postopek ponazorimo skupaj na Frobeniusovem pravilu. *)

  (** Logična oblika, s taktikami *)
  Theorem frobenius1 (A : Type) (P : A -> Prop) (Q : Prop) :
    (exists a : A, Q /\ P a) -> Q /\ exists a : A, P a.
  Proof.
    (* predavanja *)
    admit.
  Qed.

  (** Tipi (tu pišemo [(.....)%type], sicer Coq misli, da * pomeni množenje
      števil. *)
  Theorem frobenius2 (A : Type) (P : A -> Type) (Q : Type) :
    ({ a : A & Q * P a } -> Q * { a : A & P a })%type.
  Proof.
    (* predavanja *)
    admit.
  Qed.

  (** Neposredna definicija *)
  Definition frobenius3 (A : Type) (P : A -> Type) (Q : Type) :
    ({ a : A & Q * P a } -> Q * { a : A & P a })%type.
  (* predavanja *)
  Admitted.

  (** Za vajo naredi isto z obratno implikacijo. Najprej s taktikami: *)
  Theorem frobenius4 (A : Type) (P : A -> Prop) (Q : Prop) :
    (Q /\ exists a : A, P a) -> exists a : A, Q /\ P a.
  Proof.
    (* vaje *)
    admit.
  Qed.

  (** Preveri, ali isti dokaz delue tudi s tipi. *)
  Theorem frobenius5 (A : Type) (P : A -> Type) (Q : Type) :
    (Q * { a : A & P a } -> { a : A & Q * P a })%type.
  Proof.
    (* vaje *)
    admit.
  Qed.

  (** Še neposredna konstrukcija. *)
  Definition frobenius6 (A : Type) (P : A -> Type) (Q : Type) :
    (Q * { a : A & P a } -> { a : A & Q * P a })%type.
  (* vaje *)
  Admitted.

End Frobenius.

Section Vaje2.
  (** Reši s taktikami. *)  
  Lemma vaja2_1 (A B : Type) (P : A * B -> Type) :
    (forall (a : A) (b : B), P (a, b)) -> forall (b : B) (a : A), P (a, b).
  Proof.
    (* vaje *)
    admit.
  Qed.

  (** Definiraj neposredno. *)
  Definition vaja2_2 (A B : Type) (P : A * B -> Prop) :
    (forall (a : A) (b : B), P (a, b)) -> forall (b : B) (a : A), P (a, b).
  (* vaje *)
  Admitted.

  (** Definiraj s taktikami. *)
  Definition vaja2_3 (A : Type) (P : A -> Type) (Q : forall (a : A), P a -> Type) :
    (forall (a : A) (p : P a), Q a p) ->
    (forall u : {a : A & P a}, Q (projT1 u) (projT2 u)).
  Proof.
    (* vaje *)
    admit.
  Defined.

  (** Definiraj neposredno. *)
  Definition vaja2_4 (A : Type) (P : A -> Type) (Q : forall (a : A), P a -> Type) :
    (forall (a : A) (p : P a), Q a p) ->
    (forall u : {a : A & P a}, Q (projT1 u) (projT2 u)).
  (* vaje *)
  Admitted.
End Vaje2.

Section AksiomIzbire.
  (** Vprašanje: zakaj se ta sekcija imenuje Aksiom Izbire? *)

  Definition izbira1 (A B : Type) (P : A * B -> Type) :
    (forall (a : A), { b : B & P (a, b) }) -> {f : A -> B & forall (a : A), P (a, f a) }.
  Proof.
    refine (fun g => existT _ (fun a => projT1 (g a)) _).
    (* vaje *)
    admit.
  Defined.
 
  (** Ali lahko dokažeš [izbira], če ga spremeniš v logično obliko? *)
  Lemma izbira2 (A B : Type) (P : A * B -> Prop) :
    (forall (a : A), exists (b : B), P (a, b)) -> exists (f : A -> B), forall (a : A), P (a, f a).
  Proof.
    (* vaje *)
    admit.
  Qed.

  (** Reši s taktikami. *)
  Definition izbira3 (A B : Type) (P : A * B -> Type) :
    {f : A -> B & forall (a : A), P (a, f a) } -> (forall (a : A), { b : B & P (a, b) }).
  Proof.
    (* vaje *)
    admit.
  Defined.

  (** Definiraj neposredno. *)
  Definition izbira4 (A B : Type) (P : A * B -> Type) :
    {f : A -> B & forall (a : A), P (a, f a) } -> (forall (a : A), { b : B & P (a, b) }).
  (* vaje *)
  Admitted.
End AksiomIzbire.

Section Vaje3.
  (** Pa še nekaj vaj. *)

  (** Reši s taktikami. *)
  Definition Frobenius_forall1 (A : Type) (P : A -> Prop) (Q : Prop) :
    Q \/ (forall x : A, P x) -> forall (x : A), Q \/ P x.
  Proof.
    (* vaje *)
    admit.
  Qed.

  (** Definiraj neposredno. *)
  Definition Frobenius_forall2 (A : Type) (P : A -> Type) (Q : Type) :
    Q + (forall x : A, P x) -> forall (x : A), Q + P x.
  (* vaje *)
  Admitted.

  (** Pravimo, da je predikat [Q] _odločlji_, če velja [Q \/ ~Q].
      Obrat velja pod predpostavko, da je [Q] odločljiv. *)

  (** Dokaži s taktikami. *)
  Theorem Frobenius_forall3 (A : Type) (P : A -> Prop) (Q : Prop) :
    (Q \/ ~Q) ->
    (forall (x : A), Q \/ P x) -> Q \/ (forall x : A, P x).
  Proof.
    (* vaje *)
    admit.
  Qed.

  (** Definiraj neposredno. *)
  Definition Frobenius_forall4 (A : Type) (P : A -> Type) (Q : Type) :
    (Q + (Q -> Empty_set)) ->
    (forall (x : A), Q + P x) -> Q + (forall x : A, P x).
  (* Vaje *)
  Admitted.

End Vaje3.
