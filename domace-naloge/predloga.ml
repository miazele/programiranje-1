(*----------------------------------------------------------------------------*
  # 4. domača naloga
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
  ## Slovarji
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
  Na predavanjih in vajah smo si ogledali iskalna drevesa in implementacijo 
  AVL-dreves za predstavitev množic. V tej nalogi morate s pomočjo AVL-dreves 
  implementirati `slovar`, ki preslika ključe tipa `'k` v vrednosti tipa `'v`.
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
  ### Stroga ureditev

  Za predstavitev slovarja potrebujemo strogo ureditev na tipu ključev.
  Najprej definiramo tip `ureditev`, ki predstavlja možne izide
  primerjave dveh elementov, nato pa še modul `UREJEN_TIP`, s katerim
  lahko primerjamo abstraktne elemente.


[*----------------------------------------------------------------------------*)

type ureditev = Less | Equal | Greater

module type UREJEN_TIP = sig
  type t

  val primerjaj : t -> t -> ureditev
end

module INT_UREJEN_TIP : UREJEN_TIP with type t = int = struct
  type t = int

  let primerjaj x y = if x < y then Less else if x > y then Greater else Equal
end

(*----------------------------------------------------------------------------*
  Sestavite modul `STRING_UREJEN_TIP`, ki implementira `UREJEN_TIP` za tip
  `string`.
[*----------------------------------------------------------------------------*)

module STRING_UREJEN_TIP : UREJEN_TIP with type t = string = struct
  type t = string

  let primerjaj x y = if x < y then Less else if x > y then Greater else Equal
end;;

STRING_UREJEN_TIP.primerjaj "abc" "abd"
(* - : ureditev = Less *)

(*----------------------------------------------------------------------------*
  Za poljuben tip lahko definiramo `razširitev` z najmanjšim in največjim
  elementom. Sestavite parametriziran modul `RAZSIRJEN_UREJEN_TIP`, ki
  sprejme modul, ki implementira signaturo `UREJEN_TIP`, in vrne modul, ki
  implementira signaturo `UREJEN_TIP` za razširjeni tip.
[*----------------------------------------------------------------------------*)

type 'a razsiritev = MinInf | PlusInf | Value of 'a

module RAZSIRJEN_UREJEN_TIP (U : UREJEN_TIP) :
  UREJEN_TIP with type t = U.t razsiritev = struct
  type t = U.t razsiritev

  let primerjaj x y = match (x, y) with
    | (MinInf, MinInf) -> Equal
    | (PlusInf, PlusInf) -> Equal
    | (MinInf, _) -> Less
    | (PlusInf, _) -> Greater
    | (_, MinInf) -> Greater
    | (_, PlusInf) -> Less
    | (Value a, Value b) -> U.primerjaj a b
end


module LIFTED_INT_UREJEN_TIP = RAZSIRJEN_UREJEN_TIP (INT_UREJEN_TIP);;

LIFTED_INT_UREJEN_TIP.primerjaj MinInf (Value 3)
(* - : ureditev = Less *)

(*----------------------------------------------------------------------------*
  ### AVLSlovar

  Sestavite parametriziran modul `MAKE_SLOVAR`, ki sprejme modul, ki
  implementira `UREJEN_TIP`, in vrne modul s signaturo `SLOVAR`. Vaš slovar
  naj bo implementiran z AVL-drevesi, tako da je vstavljanje in iskanje v
  slovarju v času `O(log n)`.
[*----------------------------------------------------------------------------*)

module type SLOVAR = sig
  type kljuc
  type 'a t

  val prazen : 'a t
  (** Vrne prazen slovar. *)
  val dodaj : kljuc -> 'a -> 'a t -> 'a t
  (** Doda nov par `kljuc`, `vrednost` v slovar. Če ključ v slovarju že obstaja, 
      se njegova vrednost posodobi. *)
  val popravi : kljuc -> ('a option -> 'a option) -> 'a t -> 'a t
  (** Popravi vrednost pod ključem `kljuc` s funkcijo `f`. Če ključ v slovarju
      ne obstaja, se pokliče `f None`, sicer `f (Some vrednost)`. Če je rezultat
      klica `f` enak `None`, se par odstrani iz slovarja, če je rezultat klica 
      `Some v`, se pod ključ `kljuc` zapiše vrednost `v`.*)
  val odstrani : kljuc -> 'a t -> 'a t
  (** Odstrani par s ključem `kljuc` iz slovarja. Če ključa v slovarju ni, naj 
      funkcija vrne prvotni slovar in ne sproži napake. *)
  val velikost : 'a t -> int
  (** Vrne število elementov v slovarju. *)
  val kljuci : 'a t -> kljuc list
  (** Našteje ključe v slovarju v enakem vrstnem redu kot to določa urejenost. *)
  val vrednosti : 'a t -> 'a list
  (** Našteje vrednosti v slovarju v enakem vrstnem redu kot to določa urejenost
      pripadajočih ključev. *)
  val najmanjsi_opt : 'a t -> (kljuc * 'a) option
  (** Vrne najmanjši ključ v slovarju ali `None`, če je slovar prazen. *)
  val najvecji_opt : 'a t -> (kljuc * 'a) option
  (** Vrne največji ključ v slovarju ali `None`, če je slovar prazen. *)
  val poisci_opt : kljuc -> 'a t -> 'a option
  (** Poišče vrednost pod ključem `kljuc`. Če ključ v slovarju ne obstaja,
      vrne `None`. *)
  val iter : (kljuc -> 'a -> unit) -> 'a t -> unit
  (** Izvede funkcijo za vsak par ključ, vrednost v slovarju v enakem vrstnem 
      redu kot ga določa urejenost. *)
  val zlozi : (kljuc -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  (** Zloži slovar z dano funkcijo in začetno vrednostjo. Elementi se obdelajo
      v enakem vrstnem redu kot ga določa urejenost.
  
      Specifično za
      `zlozi f slovar acc = f k_n v_n (... (f k_2 v_2 (f k_1 v_1 acc))...)`
      , kjer so `(k_1, v_1), ..., (k_n, v_n)` pari ključ, vrednost v slovarju 
      urejeni po ključih.
  *)
  val preslikaj : ('a -> 'b) -> 'a t -> 'b t
  (** Preslika vrednosti v slovarju z dano funkcijo. *)
  val preslikaji : (kljuc -> 'a -> 'b) -> 'a t -> 'b t
  (** Preslika vrednosti v slovarju z dano funkcijo, ki poleg vrednosti dobi še
      pripadajoči ključ. *)
  val vsebuje : kljuc -> 'a t -> bool
  (** Preveri, ali slovar vsebuje podan ključ. *)
  val za_vse : (kljuc -> 'a -> bool) -> 'a t -> bool
  (** Preveri, ali za vse pare ključ, vrednost v slovarju velja podan pogoj. *)
  val obstaja : (kljuc -> 'a -> bool) -> 'a t -> bool
  (** Preveri, ali obstaja vsaj en par ključ, vrednost v slovarju, ki izpolnjuje
      podan pogoj. *)
  val v_seznam : 'a t -> (kljuc * 'a) list
  (** Pretvori slovar v seznam parov ključ, vrednost v enakem vrstnem redu kot
      to določa urejenost. *)
  val iz_seznama : (kljuc * 'a) list -> 'a t
  (** Ustvari slovar iz seznama parov ključ, vrednost. Če se ključi v seznamu
      ponavljajo, naj enak ključ obdrži zadnjo vrednost. *)
end


module MAKE_SLOVAR (U : UREJEN_TIP) : SLOVAR with type kljuc = U.t = struct
  type kljuc = U.t
  type 'a t = Prazno | Sestavljeno of int * 'a t * kljuc * 'a * 'a t
                              (* višina, levo, ključ, vrednost, desno *)

  let prazen : 'a t = Prazno
 
  (* prej dodamo še nekaj pomožnih funkcij za lažjo definicijo "dodaj" *)
  let visina drevo =
    match drevo with
    | Prazno -> 0
    | Sestavljeno (h, _, _, _, _) -> h

  let sestavljeno (l, k, v, d) = Sestavljeno (1 + max (visina l) (visina d), l, k, v, d)

  let zavrti_levo = function
    | Sestavljeno (_, l, k, kv, Sestavljeno (_, dl, n, nv, dd)) ->
        sestavljeno (sestavljeno (l, k, kv, dl), n, nv, dd)
    | _ -> failwith "Tega drevesa ne morem zavrteti"

  let zavrti_desno = function
    | Sestavljeno (_, Sestavljeno (_, ll, n, nv, ld), k, kv, d) ->
        sestavljeno (ll, n, nv, sestavljeno (ld, k, kv, d))
    | _ -> failwith "Tega drevesa ne morem zavrteti"

  let razlika = function
    | Prazno -> 0
    | Sestavljeno (_, l, _, _, d) -> visina l - visina d

  let uravnotezi drevo =
    match drevo with
    | Sestavljeno (_, l, k, v, d) when razlika drevo = 2 && razlika l = 1 ->
        zavrti_desno drevo
    | Sestavljeno (_, l, k, v, d) when razlika drevo = 2 ->
        sestavljeno (zavrti_levo l, k, v, d) |> zavrti_desno
    | Sestavljeno (_, l, k, v, d) when razlika drevo = -2 && razlika d = -1 ->
        zavrti_levo drevo
    | Sestavljeno (_, l, k, v, d) when razlika drevo = -2 ->
        sestavljeno (l, k, v, zavrti_desno d) |> zavrti_levo
    | _ -> drevo

  let rec dodaj k v drevo = match drevo with
  | Prazno -> Sestavljeno (1, Prazno, k, v, Prazno)
  | Sestavljeno (h, l, kljuc, vrednost, d) ->
      match U.primerjaj k kljuc with
      | Less -> sestavljeno (dodaj k v l, kljuc, vrednost, d) |> uravnotezi
      | Greater -> sestavljeno (l, kljuc, vrednost, dodaj k v d) |> uravnotezi
      | Equal -> Sestavljeno (h, l, k, v, d)

  
  let rec odstrani k slovar = match slovar with
  | Prazno -> Prazno
  | Sestavljeno (_, l, kljuc, vrednost, d) as tree -> 
    match U.primerjaj k kljuc with
    | Less -> sestavljeno (odstrani k l, kljuc, vrednost, d) |> uravnotezi
    | Greater -> sestavljeno (l, kljuc, vrednost, odstrani k d) |> uravnotezi
    | Equal -> let succ drevo =  (* potrebujemo naslednika *)
                  let rec minimalen = function
                    | Prazno -> None
                    | Sestavljeno (_, Prazno, x, y, _) -> Some (x, y)
                    | Sestavljeno (_, l, _, _, _) -> minimalen l in
                  match drevo with
                  | Prazno -> None
                  | Sestavljeno (_, l, x, _, d) -> minimalen d in
                
                match succ tree with
                | None -> l
                | Some (a, b) -> sestavljeno (l, a, b, odstrani a d) |> uravnotezi

  let rec popravi k f slovar = 
    match slovar with
    | Prazno -> 
      (match f None with
      | None -> Prazno
      | Some a -> dodaj k a Prazno)
    | Sestavljeno (h, l, kljuc, vrednost, d) -> 
      match U.primerjaj k kljuc with
      | Less -> let novo_levo = popravi k f l in uravnotezi (sestavljeno (novo_levo, kljuc, vrednost, d))
      | Greater -> let novo_desno = popravi k f d in uravnotezi (sestavljeno (l, kljuc, vrednost, novo_desno))
      | Equal -> match f (Some vrednost) with
        | Some a -> Sestavljeno (h, l, kljuc, a, d)
        | None -> odstrani k slovar

  let rec velikost = function
    | Prazno -> 0
    | Sestavljeno (_, l, _, _, d) -> 1 + velikost l + velikost d

  let kljuci slovar = 
    let rec aux acc = function
    | Prazno -> acc
    | Sestavljeno (_, l, k, _, d) -> aux (k :: aux acc d) l in 
    aux [] slovar

  let rec vrednosti slovar =
    let rec aux acc = function
    | Prazno -> acc
    | Sestavljeno (_, l, _, v, d) -> aux (v :: aux acc d) l in
    aux [] slovar

  let rec najmanjsi_opt = function
    | Prazno -> None
    | Sestavljeno (_, Prazno, k, v, _) -> Some (k, v)
    | Sestavljeno (_, l, _, _, _) -> najmanjsi_opt l

  let rec najvecji_opt = function
    | Prazno -> None
    | Sestavljeno (_, _, k, v, Prazno) -> Some (k, v)
    | Sestavljeno (_, _, _, _, d) -> najvecji_opt d

  let rec poisci_opt k = function
    | Prazno -> None
    | Sestavljeno (_, l, kljuc, v, d) -> match U.primerjaj k kljuc with
                                          | Less -> poisci_opt k l
                                          | Greater -> poisci_opt k d
                                          | Equal -> Some v

  let iter f slovar = 
    let rec aux = function
    | Prazno -> ()
    | Sestavljeno (_, l, k, v, d) ->
        aux l;
        f k v;
        aux d in
    aux slovar

  let rec zlozi f slovar acc = 
    match slovar with
    | Prazno -> acc
    | Sestavljeno (_, l, k, v, d) -> 
      let acc1 = zlozi f l acc in
      let acc2 = f k v acc1 in
      zlozi f d acc2                   

  let rec preslikaj f slovar = 
    match slovar with
    | Prazno -> Prazno
    | Sestavljeno (h, l, k, v, d) -> Sestavljeno (h, preslikaj f l, k, f v, preslikaj f d)

  let rec preslikaji f slovar = 
    match slovar with
    | Prazno -> Prazno
    | Sestavljeno (h, l, k, v, d) -> Sestavljeno (h, preslikaji f l, k, f k v, preslikaji f d)
  
  let rec vsebuje k slovar = 
    match slovar with
    | Prazno -> false
    | Sestavljeno (_, l, kljuc, _, d) -> 
      match U.primerjaj k kljuc with
      | Less -> vsebuje k l
      | Greater -> vsebuje k d
      | Equal -> true

  let rec za_vse f slovar = 
    match slovar with
    | Prazno -> true
    | Sestavljeno (_, l, k, v, d) -> za_vse f l && f k v && za_vse f d
  
  let rec obstaja f slovar = 
    match slovar with
    | Prazno -> false
    | Sestavljeno (_, l, k, v, d) -> za_vse f l || f k v || za_vse f d
  
  let v_seznam slovar =
    let rec aux acc = function
    | Prazno -> acc
    | Sestavljeno (_, l, k, v, d) -> aux ((k, v) :: aux acc d) l in 
    aux [] slovar
  
  let iz_seznama list = 
    let rec aux acc = function 
    | [] -> acc
    | (k, v) :: xs -> aux (dodaj k v acc) xs
    in aux Prazno list
end

module SLOVAR_NIZ = MAKE_SLOVAR (STRING_UREJEN_TIP)

let slovar =
  SLOVAR_NIZ.iz_seznama
    [ ("jabolko", "apple"); ("banana", "banana"); ("cesnja", " cherry") ]
  |> SLOVAR_NIZ.dodaj "datelj" "date"
  |> SLOVAR_NIZ.odstrani "banana"
  |> SLOVAR_NIZ.popravi "cesnja" (function
       | None -> Some "cherry"
       | Some v -> Some ("sour " ^ v))
  |> SLOVAR_NIZ.preslikaj String.length
  |> SLOVAR_NIZ.v_seznam


(*----------------------------------------------------------------------------*
  ## Turingovi stroji
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
  Na predavanjih in vajah smo si ogledali Turingove stroje. Pred vami je
  neučinkovito implementiran Turingov stroj. Vaša naloga je, da implementacijo
  s pomočjo slovarjev izboljšate tako, da bo deloval učinkoviteje.
[*----------------------------------------------------------------------------*)

type direction = Left | Right
type state = string

module type TAPE = sig
  type t

  val make : string -> t
  val print : t -> unit
  val read : t -> char
  val move : direction -> t -> t
  val write : char -> t -> t
end

module Tape : TAPE = struct
  type t = { left : char list; right : char list }

  let make str = { left = []; right = str |> String.to_seq |> List.of_seq }

  let print { left; right } =
    List.rev_append left right |> List.to_seq |> String.of_seq |> print_endline;
    print_endline (String.make (List.length left) ' ' ^ "^")

  let read { right } = match right with [] -> ' ' | chr :: _ -> chr

  let move dir { left; right } =
    match (dir, left, right) with
    | Left, ' ' :: left, [] -> { left; right }
    | Left, chr :: left, right -> { left; right = chr :: right }
    | Left, [], right -> { left = []; right = ' ' :: right }
    | Right, [], ' ' :: right -> { left; right }
    | Right, left, chr :: right -> { left = chr :: left; right }
    | Right, left, [] -> { left = ' ' :: left; right = [] }

  let write chr { left; right } =
    match right with
    | [] when chr = ' ' -> { left; right }
    | [] -> { left; right = [ chr ] }
    | _ :: right -> { left; right = chr :: right }
end


let primer_trak =
  Tape.(
    make "ABCDE" |> move Left |> move Left |> move Right |> move Right
    |> move Right |> move Right |> write '!' |> print)

module type MACHINE = sig
  type t

  val make : state -> state list -> t
  val initial : t -> state
  val add_transition : state -> char -> state -> char -> direction -> t -> t
  val step : t -> state -> Tape.t -> (state * Tape.t) option
  val run : t -> state -> unit
  val speed_run : t -> state -> unit
end

module MachineNeucinkovito : MACHINE = struct
  type t = {
    initial : state;
    transitions : (state * char * state * char * direction) list;
  }

  let make initial _states = { initial; transitions = [] }
  let initial { initial } = initial

  let add_transition st chr st' chr' dir tm =
    { tm with transitions = (st, chr, st', chr', dir) :: tm.transitions }

  let step tm st tape =
    let chr = Tape.read tape in
    match
      List.find_opt
        (fun (st', chr', _, _, _) -> st = st' && chr = chr')
        tm.transitions
    with
    | None -> None
    | Some (_, _, st', chr', dir) ->
        Some (st', tape |> Tape.write chr' |> Tape.move dir)

  let run tm str =
    let rec step' (st, tape) =
      (Tape.print tape;
      print_endline st;
      match step tm st tape with
      | None -> ()
      | Some config' -> step' config')
    in
    step' (initial tm, Tape.make str)

  let speed_run tm str =
  let rec step' (st, tape) =
    match step tm st tape with
    | None -> Tape.print tape
    | Some config' -> step' config'
  in
  step' (initial tm, Tape.make str)
end

(*----------------------------------------------------------------------------*
  Sestavite modul `MachineUcinkovito`, ki učinkovito implementira signaturo
  `MACHINE` z uporabo slovarja, ki ste ga implementirali pred tem. Na kratko
  analizirajte časovno zahtevnost operacij `add_transition` in `step` v
  primerjavi z neučinkovito implementacijo.

  Namig:  
  Za dodatne točke je časovna zahtevnost iskanja prehoda v funkciji
  `speed_run` z nekaj preprocesiranja konstantna.
[*----------------------------------------------------------------------------*)

module MachineUcinkovito : MACHINE = struct
  (* Najprej definiramo tip za prehod (vrednost v slovarju) *)
  type prehod = {
    novo_stanje : state;
    zapisani_znak : char;
    smer : direction
  }

  (* Tip stroja *)
  type t = {
    initial : state;
    prehodi : prehod SLOVAR_NIZ.t  (* slovar s ključi (state * char) *)
  }

  (* Pomožna funkcija za pretvorbo ključa v niz za slovar *)
  let kljuc_v_niz (s, c) = s ^ String.make 1 c
  
  let make initial _states = { initial; prehodi = SLOVAR_NIZ.prazen }

  let initial { initial } = initial

  let add_transition st chr st' chr' dir tm = 
    let kljuc = kljuc_v_niz (st, chr) in
    let nov_prehod = { novo_stanje = st'; zapisani_znak = chr'; smer = dir } in
    { tm with prehodi = SLOVAR_NIZ.dodaj kljuc nov_prehod tm.prehodi }

  let step tm st tape = 
    let chr = Tape.read tape in
    let kljuc = kljuc_v_niz (st, chr) in
    match SLOVAR_NIZ.poisci_opt kljuc tm.prehodi with
    | None -> None
    | Some { novo_stanje; zapisani_znak; smer } -> Some (novo_stanje, tape |> Tape.write zapisani_znak |> Tape.move smer)

  let run tm str =
    let rec step' (st, tape) =
      Tape.print tape;
      print_endline st;
      match step tm st tape with
      | None -> ()
      | Some config' -> step' config'
    in
    step' (initial tm, Tape.make str)
  
  let speed_run tm str =
    let rec step' (st, tape) =
      match step tm st tape with
      | None -> Tape.print tape
      | Some config' -> step' config'
    in
    step' (initial tm, Tape.make str)
end

(* Analiza časovne zahtevnosti add_transition : v MachineNeucinkovito je časovna zahtevnost O(1), saj se doda nov element na začetek seznama;
    v MachineUcinkovito je časovna zahtevnost O(log n), saj uporablja AVL slovar, višina drevesa je približno log n *)

(* Analiza časovne zahtevnosti step : v MachineNeucinkovito je časovna zahtevnost O(n), saj List.find_opt preišče cel seznam;
    v MachineUcinkovito je časovna zahtevnost O(log n), saj SLOVAR_NIZ.poisci_opt išče po drevesu - največ log n korakov do najdenega elementa *)



(*----------------------------------------------------------------------------*
  Sestavite Turingov stroj, ki na vhodnem nizu prepozna palindrom (iz `0` in
  `1`). Če je na vhodnem nizu palindrom, naj na koncu na traku zapiše `1`,
  sicer `0`.
[*----------------------------------------------------------------------------*)

let palindrom_stroj : MachineUcinkovito.t = let open MachineUcinkovito in
  make "start" []
  
  (* start *)
  |> add_transition "start" '0' "haveZero" ' ' Right
  |> add_transition "start" '1' "haveOne" ' ' Right
  |> add_transition "start" ' ' "write1" ' ' Left
  
  (* haveZero *)
  |> add_transition "haveZero" '0' "haveZero" '0' Right
  |> add_transition "haveZero" '1' "haveZero" '1' Right
  |> add_transition "haveZero" ' ' "matchZero" ' ' Left
  
  (* haveOne *)
  |> add_transition "haveOne" '0' "haveOne" '0' Right
  |> add_transition "haveOne" '1' "haveOne" '1' Right
  |> add_transition "haveOne" ' ' "matchOne" ' ' Left
  
  (* matchZero *)
  |> add_transition "matchZero" '0' "back" ' ' Left    
  |> add_transition "matchZero" '1' "write0" ' ' Left  
  |> add_transition "matchZero" ' ' "write1" ' ' Left  
  
  (* matchOne *)
  |> add_transition "matchOne" '0' "write0" ' ' Left  
  |> add_transition "matchOne" '1' "back" ' ' Left    
  |> add_transition "matchOne" ' ' "write1" ' ' Left  
  
  (* back *)
  |> add_transition "back" '0' "back" '0' Left
  |> add_transition "back" '1' "back" '1' Left
  |> add_transition "back" ' ' "start" ' ' Right 
  
  (* write1 *)
  |> add_transition "write1" '0' "write1" '0' Right
  |> add_transition "write1" '1' "write1" '1' Right
  |> add_transition "write1" ' ' "halt" '1' Left  
  
  (* write0 *)
  |> add_transition "write0" '0' "write0" '0' Right
  |> add_transition "write0" '1' "write0" '1' Right
  |> add_transition "write0" ' ' "halt" '0' Left
  
  (* halt -> končno stanje *)

let test1 = MachineUcinkovito.speed_run palindrom_stroj "101"  (* palindrom -> 1 *)  
let test2 = MachineUcinkovito.speed_run palindrom_stroj "100"  (* ni palindrom -> 0 *)  
let test3 = MachineUcinkovito.speed_run palindrom_stroj ""     (* prazen -> 1 *)  
let test4 = MachineUcinkovito.speed_run palindrom_stroj "0"    (* en znak -> 1 *)  

(*----------------------------------------------------------------------------*
  Sestavite Turingov stroj, ki na vhod sprejme niz `n` enic in na koncu na
  traku zapiše `n^2` enic.
[*----------------------------------------------------------------------------*)

let kvadrat_stroj : MachineUcinkovito.t = let open MachineUcinkovito in
  make "start" []
  
  (* start *)
  |> add_transition "start" '1' "start" '1' Right
  |> add_transition "start" ' ' "spotX" '#' Left
  
  (* spotX *)
  |> add_transition "spotX" '1' "spotX" '1' Left
  |> add_transition "spotX" 'Y' "spotX" 'Y' Left
  |> add_transition "spotX" 'Z' "spotX" 'Z' Left
  |> add_transition "spotX" 'X' "addX" 'X' Right
  |> add_transition "spotX" ' ' "addX" ' ' Right
  
  (* addX *)
  |> add_transition "addX" '1' "backToStart" 'X' Left
  |> add_transition "addX" 'Z' "backToStart" 'X' Left
  |> add_transition "addX" '#' "findEnd" '#' Left
  
  (* findEnd *)
  |> add_transition "findEnd" 'X' "findEnd" 'X' Left
  |> add_transition "findEnd" ' ' "clean" ' ' Right
  
  (* clean - both X and # have same transition *)
  |> add_transition "clean" 'X' "clean" ' ' Right
  |> add_transition "clean" '#' "clean" ' ' Right
  |> add_transition "clean" '1' "end" '1' Left
  
  (* backToStart *)
  |> add_transition "backToStart" ' ' "check" ' ' Right
  |> add_transition "backToStart" 'X' "backToStart" 'X' Left
  |> add_transition "backToStart" 'Y' "backToStart" 'Y' Left
  |> add_transition "backToStart" '1' "backToStart" '1' Left
  
  (* check *)
  |> add_transition "check" 'X' "goToEnd" 'Y' Right
  
  (* goToEnd *)
  |> add_transition "goToEnd" 'X' "goToEnd" 'X' Right
  |> add_transition "goToEnd" 'Y' "goToEnd" 'Y' Right
  |> add_transition "goToEnd" 'Z' "goToEnd" 'Z' Right
  |> add_transition "goToEnd" '#' "goToEnd" '#' Right
  |> add_transition "goToEnd" '1' "goToEnd" '1' Right
  |> add_transition "goToEnd" ' ' "findYZ" '1' Left
  
  (* findYZ *)
  |> add_transition "findYZ" 'X' "findYZ" 'X' Left
  |> add_transition "findYZ" '1' "findYZ" '1' Left
  |> add_transition "findYZ" '#' "findYZ" '#' Left
  |> add_transition "findYZ" 'Y' "writeYZ" 'Y' Right
  |> add_transition "findYZ" 'Z' "writeYZ" 'Z' Right
  
  (* writeYZ *)
  |> add_transition "writeYZ" '1' "goToEnd" 'Z' Right
  |> add_transition "writeYZ" 'X' "goToEnd" 'Y' Right
  |> add_transition "writeYZ" '#' "rewrite" '#' Left
  
  (* rewrite *)
  |> add_transition "rewrite" 'Y' "rewrite" 'X' Left
  |> add_transition "rewrite" 'Z' "rewrite" '1' Left
  |> add_transition "rewrite" ' ' "findHash" ' ' Right
  
  (* findHash *)
  |> add_transition "findHash" 'X' "findHash" 'X' Right
  |> add_transition "findHash" '1' "findHash" '1' Right
  |> add_transition "findHash" '#' "spotX" '#' Left
  
  (* end - končmno stanje *)


let test11 = MachineUcinkovito.speed_run kvadrat_stroj "1111"  (* palindrom -> 1 *)  
let test12 = MachineUcinkovito.speed_run kvadrat_stroj "111"  (* ni palindrom -> 0 *)  
let test13 = MachineUcinkovito.speed_run kvadrat_stroj "11"     (* prazen -> 1 *)  
let test14 = MachineUcinkovito.speed_run kvadrat_stroj "1"    (* en znak -> 1 *)  
(*----------------------------------------------------------------------------*
  Sestavite Turingov stroj, ki na začetku na traku sprejme število `n`,
  zapisano v dvojiškem zapisu, na koncu pa naj bo na traku zapisanih
  natanko `n` enic.
[*----------------------------------------------------------------------------*)

(* pri reševanju predpostavimo, da je n naravno število :) *)

let enice_stroj : MachineUcinkovito.t = let open MachineUcinkovito in
  make "init" []

  (* init *)
  |> add_transition "init" '0' "init" '0' Right
  |> add_transition "init" '1' "init" '1' Right
  |> add_transition "init" ' ' "addCounter" '#' Right
  
  (* addCounter *)
  |> add_transition "addCounter" '0' "addCounter" '0' Right
  |> add_transition "addCounter" '1' "addCounter" '1' Right
  |> add_transition "addCounter" '#' "addCounter" '#' Right
  |> add_transition "addCounter" ' ' "backToNumber" '1' Left

  (* backToNumber *)
  |> add_transition "backToNumber" '0' "backToNumber" '0' Left
  |> add_transition "backToNumber" '1' "backToNumber" '1' Left
  |> add_transition "backToNumber" '#' "backToNumber" '#' Left
  |> add_transition "backToNumber" ' ' "start" ' ' Right

  (* start *)
  |> add_transition "start" '0' "start" '0' Right
  |> add_transition "start" '1' "start" '1' Right
  |> add_transition "start" '#' "decrement" '#' Left
  |> add_transition "start" ' ' "decrement" ' ' Left

  (* decrement *)
  |> add_transition "decrement" '0' "carry" '1' Left
  |> add_transition "decrement" '1' "backToStart" '0' Left
  |> add_transition "decrement" ' ' "backToStart" ' ' Left

  (* carry *)
  |> add_transition "carry" '1' "backToStart" '0' Left
  |> add_transition "carry" '0' "carry" '1' Left
  |> add_transition "carry" ' ' "backToStart" ' ' Left

  (* backToStart *)
  |> add_transition "backToStart" '0' "backToStart" '0' Left
  |> add_transition "backToStart" '1' "backToStart" '1' Left
  |> add_transition "backToStart" ' ' "removeZeros" ' ' Right

  (* removeZeros *)
  |> add_transition "removeZeros" '0' "removeZeros" ' ' Right
  |> add_transition "removeZeros" '1' "moveRight" '1' Left
  |> add_transition "removeZeros" ' ' "moveRight" ' ' Left
  |> add_transition "removeZeros" '#' "halt" ' ' Right

  (* moveRight *)
  |> add_transition "moveRight" '0' "addOne" '0' Right
  |> add_transition "moveRight" '1' "addOne" '1' Right
  |> add_transition "moveRight" ' ' "addOne" ' ' Right
  |> add_transition "moveRight" '#' "addOne" '#' Right

  (* addOne *)
  |> add_transition "addOne" '0' "addOne" '0' Right
  |> add_transition "addOne" '1' "addOne" '1' Right
  |> add_transition "addOne" '#' "addOne" '#' Right
  |> add_transition "addOne" ' ' "backToNumber" '1' Left

  (* halt -> končno stanje *)

let test99 = MachineUcinkovito.speed_run enice_stroj "101"
let test98 = MachineUcinkovito.speed_run enice_stroj "100"
let test97 = MachineUcinkovito.speed_run enice_stroj "11"
let test96 = MachineUcinkovito.speed_run enice_stroj "1"

(*----------------------------------------------------------------------------*
  Sestavite ravno obratni Turingov stroj, torej tak, ki na začetku na traku
  sprejme število `n` enic, na koncu pa naj bo na traku zapisano število `n`
  v dvojiškem zapisu.
[*----------------------------------------------------------------------------*)

let dvojski_stroj : MachineUcinkovito.t = let open MachineUcinkovito in
  make "start" []

  (* start *)
  |> add_transition "start" '1' "addCounter" '1' Left

  (* addCounter *)
  |> add_transition "addCounter" ' ' "addZero" '#' Left

  (* addZero *)
  |> add_transition "addZero" ' ' "goToEnd" '0' Right

  (* goToEnd *)
  |> add_transition "goToEnd" '1' "goToEnd" '1' Right
  |> add_transition "goToEnd" '#' "goToEnd" '#' Right
  |> add_transition "goToEnd" '0' "goToEnd" '0' Right
  |> add_transition "goToEnd" ' ' "deleteLastOne" ' ' Left

  (* deleteLastOne *)
  |> add_transition "deleteLastOne" '1' "goToStart" ' ' Left
  |> add_transition "deleteLastOne" '#' "done" ' ' Left

  (* goToStart *)
  |> add_transition "goToStart" '1' "goToStart" '1' Left
  |> add_transition "goToStart" '#' "carry" '#' Left

  (* carry *)
  |> add_transition "carry" '1' "carry" '0' Left
  |> add_transition "carry" '0' "goToEnd" '1' Right
  |> add_transition "carry" ' ' "goToEnd" '1' Right

  (* done -> končno stanje *)

let test89 = MachineUcinkovito.speed_run dvojski_stroj "111111"
let test88 = MachineUcinkovito.speed_run dvojski_stroj "11111"
let test87 = MachineUcinkovito.speed_run dvojski_stroj "1111"
let test86 = MachineUcinkovito.speed_run dvojski_stroj "1"

(*----------------------------------------------------------------------------*
  Sestavite Turingov stroj, ki na začetku na traku sprejme oklepaje `(` in
  `)`, `[` in `]` ter `{` in `}`. Stroj naj na traku izpiše `1`, če so
  oklepaji pravilno uravnoteženi in gnezdeni, ter `0` sicer.
[*----------------------------------------------------------------------------*)

let uravnotezeni_oklepaji_stroj : MachineUcinkovito.t = let open MachineUcinkovito in
  make "start" []

  (* start *)
  |> add_transition "start" ' ' "accept" ' ' Left
  |> add_transition "start" '#' "start" ' ' Right
  |> add_transition "start" '(' "openParen" '(' Right
  |> add_transition "start" ')' "reject" ')' Left
  |> add_transition "start" '[' "openBracket" '[' Right
  |> add_transition "start" ']' "reject" ']' Left
  |> add_transition "start" '{' "openBrace" '{' Right
  |> add_transition "start" '}' "reject" '}' Left

  (* openParen *)
  |> add_transition "openParen" ' ' "reject" ' ' Left
  |> add_transition "openParen" '#' "openParen" '#' Right
  |> add_transition "openParen" '(' "openParen" '(' Right
  |> add_transition "openParen" ')' "closedParen" '#' Left
  |> add_transition "openParen" '[' "openBracket" '[' Right
  |> add_transition "openParen" ']' "reject" ']' Left
  |> add_transition "openParen" '{' "openBrace" '{' Right
  |> add_transition "openParen" '}' "reject" '}' Left

  (* openBracket *)
  |> add_transition "openBracket" ' ' "reject" ' ' Left
  |> add_transition "openBracket" '#' "openBracket" '#' Right
  |> add_transition "openBracket" '(' "openParen" '(' Right
  |> add_transition "openBracket" ')' "reject" ')' Left
  |> add_transition "openBracket" '[' "openBracket" '[' Right
  |> add_transition "openBracket" ']' "closedBracket" '#' Left
  |> add_transition "openBracket" '{' "openBrace" '{' Right
  |> add_transition "openBracket" '}' "reject" '}' Left

  (* openBrace *)
  |> add_transition "openBrace" ' ' "reject" ' ' Left
  |> add_transition "openBrace" '#' "openBrace" '#' Right
  |> add_transition "openBrace" '(' "openParen" '(' Right
  |> add_transition "openBrace" ')' "reject" ')' Left
  |> add_transition "openBrace" '[' "openBracket" '[' Right
  |> add_transition "openBrace" ']' "reject" ']' Left
  |> add_transition "openBrace" '{' "openBrace" '{' Right
  |> add_transition "openBrace" '}' "closedBrace" '#' Left
  
  (* closedParen *)
  |> add_transition "closedParen" ' ' "reject" ' ' Right
  |> add_transition "closedParen" '#' "closedParen" '#' Left
  |> add_transition "closedParen" '(' "repeat" '#' Left
  |> add_transition "closedParen" ')' "closedParen" ')' Left
  |> add_transition "closedParen" '[' "reject" '[' Left
  |> add_transition "closedParen" ']' "closedBracket" ']' Left
  |> add_transition "closedParen" '{' "reject" '{' Left
  |> add_transition "closedParen" '}' "closedBrace" '}' Left

  (* closedBracket *)
  |> add_transition "closedBracket" ' ' "reject" ' ' Right
  |> add_transition "closedBracket" '#' "closedBracket" '#' Left
  |> add_transition "closedBracket" '(' "reject" '(' Left
  |> add_transition "closedBracket" ')' "closedParen" ')' Left
  |> add_transition "closedBracket" '[' "repeat" '#' Left
  |> add_transition "closedBracket" ']' "closedBracket" ']' Left
  |> add_transition "closedBracket" '{' "reject" '{' Left
  |> add_transition "closedBracket" '}' "closedBrace" '}' Left

  (* closedBrace *)
  |> add_transition "closedBrace" ' ' "reject" ' ' Right
  |> add_transition "closedBrace" '#' "closedBrace" '#' Left
  |> add_transition "closedBrace" '(' "reject" '(' Left
  |> add_transition "closedBrace" ')' "closedParen" ')' Left
  |> add_transition "closedBrace" '[' "reject" '[' Left
  |> add_transition "closedBrace" ']' "closedBracket" ']' Left
  |> add_transition "closedBrace" '{' "repeat" '#' Left
  |> add_transition "closedBrace" '}' "closedBrace" '}' Left

  (* repeat *)
  |> add_transition "repeat" ' ' "start" ' ' Right
  |> add_transition "repeat" '#' "repeat" '#' Left
  |> add_transition "repeat" '(' "openParen" '(' Right
  |> add_transition "repeat" ')' "repeat" ')' Left
  |> add_transition "repeat" '[' "openBracket" '[' Right
  |> add_transition "repeat" ']' "repeat" ']' Left
  |> add_transition "repeat" '{' "openBrace" '{' Right
  |> add_transition "repeat" '}' "repeat" '}' Left

  (* accept *)
  |> add_transition "accept" ' ' "halt" '1' Left
  |> add_transition "accept" '0' "accept" ' ' Right
  |> add_transition "accept" '1' "accept" ' ' Right
  |> add_transition "accept" '#' "accept" ' ' Right
  |> add_transition "accept" '(' "accept" ' ' Right
  |> add_transition "accept" ')' "accept" ' ' Right
  |> add_transition "accept" '[' "accept" ' ' Right
  |> add_transition "accept" ']' "accept" ' ' Right
  |> add_transition "accept" '{' "accept" ' ' Right
  |> add_transition "accept" '}' "accept" ' ' Right

  (* reject *)
  |> add_transition "reject" ' ' "halt" '0' Left
  |> add_transition "reject" '0' "reject" ' ' Right
  |> add_transition "reject" '1' "reject" ' ' Right
  |> add_transition "reject" '#' "reject" ' ' Right
  |> add_transition "reject" '(' "reject" ' ' Right
  |> add_transition "reject" ')' "reject" ' ' Right
  |> add_transition "reject" '[' "reject" ' ' Right
  |> add_transition "reject" ']' "reject" ' ' Right
  |> add_transition "reject" '{' "reject" ' ' Right
  |> add_transition "reject" '}' "reject" ' ' Right

  (* halt -> končno stanje *)


let test59 = MachineUcinkovito.speed_run uravnotezeni_oklepaji_stroj "((()))()"
let test58 = MachineUcinkovito.speed_run uravnotezeni_oklepaji_stroj "{([])}[()]"
let test57 = MachineUcinkovito.speed_run uravnotezeni_oklepaji_stroj "([)]"
let test56 = MachineUcinkovito.speed_run uravnotezeni_oklepaji_stroj "{{]}}"
let test55 = MachineUcinkovito.speed_run uravnotezeni_oklepaji_stroj "{"