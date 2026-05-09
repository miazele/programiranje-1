**1\. Katere osnovne in sestavljene vgrajene tipe poznamo in kdaj uporabljamo katerega?**

Osnovni: cela št. int, števila s plavajočo vejico float, nizi string, logične vrednosti bool, enotski tip unit, zanki char
Sestavljeni: seznami, nabori, morebitne vrednosti τ option

**2\. Kaj so funkcije višjega reda?**

Kadar funkcija za argument sprejme drugo funkcijo, govorimo o funkcijah višjega reda, npr.  String.exists. Običajne funkcije med števili, nizi, seznami in podobnimi vrednostmi so funkcije prvega reda. 

**3\. Kaj so anonimne funkcije in kje jih uporabljamo?**

Nepoimenovane funkcije oblike fun arg -> ... Npr. 
let zrcali niz =
  let n = String.length niz in
  String.init n (fun i -> String.get niz (n - i - 1))

**4\. Kaj so polimorfne funkcije in katere ste najpogosteje uporabljali?**

Funkcije, ki kot argumente lahko sprejmejo vrednosti "podobnih" tipov.
List.rev, List.flatten, List.filter

**5\. Kaj so Curryjrane funkcije in v kakšnem odnosu so z običajnimi funkcijami, ki sprejmejo nabor več argumentov?**

Curryrane funkcije so funkcije, ki sprejmejo argumente enega za drugim, pri čemer vsak klic vrne novo funkcijo za naslednji argument. Na primer: int -> int -> int (kar pomeni int -> (int -> int)).

Običajne (nekurryrane) funkcije pa sprejmejo vse argumente hkrati v obliki nabora (tupla): int * int -> int.

Njun odnos: Tipa A -> B -> C in A * B -> C sta izomorfna – vsebinsko enaka, le oblikovno različna. Zato lahko s pomočjo funkcij curry in uncurry pretvarjamo med njima:

curry : ('a * 'b -> 'c) -> 'a -> 'b -> 'c pretvori običajno funkcijo v curryrano.
uncurry : ('a -> 'b -> 'c) -> 'a * 'b -> 'c pretvori curryrano v običajno.
Prednost curryranih: omogočajo delno uporabo (podamo le prvi argument, dobimo funkcijo za preostale), kar je zelo uporabno pri funkcijah višjega reda (npr. List.map (zmnozi 6) [1;2;3]). Običajne funkcije tega ne omogočajo.


**6\. Kako gnezdimo funkcijske tipe pri funkcijah več argumentov?**

V OCamlu so funkcije več argumentov curryrane, kar pomeni, da so gnezdene funkcije enega argumenta. Definicija fun x y -> ... je okrajšava za fun x -> fun y -> ..., zato je funkcijski tip desno asociativen: int -> int -> int pomeni int -> (int -> int). To omogoča delno uporabo funkcij (npr. zmnozi 2 vrne funkcijo int -> int).

**7\. Kakšna je razlika med statičnimi in dinamičnimi tipi?**

Glede na to, kdaj se preverjajo tipi: OCaml tipe preverja statično, torej še pred izvajanjem, Python pa šele za tem, ko poženemo program.

**8\. Kaj so repni klici, kaj so repno rekurzivne funkcije in kdaj jih uporabljamo? Kako bi običajno funkcijo pretvorili v repno rekurzivno?**

Pravimo, da je klic funkcije repen, če se izvede kot zadnji korak v definiciji funkcije. Če je rekurzivni klic funkcije repen, taki funkciji pravimo repno rekurzivna. Običajno funkcijo bi pretvorili v repno rekurzivno z uporabo akumulatorja.

**9\. Kaj so zapisni in naštevni tipi? Za kaj jih uporabljamo?**

Primer zapisnih tipov: type kartezicno = {re : float; im : float}
type polarno = {radij : float; kot : float}
type datum = { dan : int; mesec : int; leto : int }

Primer naštevnih tipov: type dostava =
  | OsebniPrevzem
  | PoPosti

type posiljka = {
  naslovnik : string;
  naslov : string;
  dostava : dostava
}

Razlika med njimi je v tem, da morajo biti pri zapisnih tipih prisotne vrednosti vseh naštetih polj, mora biti pri naštevnih tipih prisotna natanko ena izmed naštetih variant.

**10\. Katere osnovnim matematičnim konstrukcijam ustrezajo naštevni tipi?**

Geometrijski objekti

**11\. Kaj so algebrajski tipi in kaj so najbolj znani primeri takih tipov?**

Naštevni tipi, ki so rekruzivni, npr. naravna števila, verižni seznami, aritmetični izrazi, dvojiška drevesa.

**12\. Iz česa so sestavljeni moduli in iz česa signature? Kdaj modul ustreza dani signaturi?**

OCamlovi moduli so zbirke definicij tipov, funkcij, vrednosti, (kasneje tudi drugih modulov), kot smo jih do sedaj pisali v datoteke ali v ukazno vrstico. V resnici vsaka .ml datoteka predstavlja modul, ki vsebuje vse definicije v njej. Do sedaj smo spoznali že nekaj modulov iz standardne knjižnice: String za delo z nizi, List za delo s seznami ali Random za delo z naključnimi vrednostmi.

Tako kot ima vsaka vrednost v OCamlu svoj tip, lahko zgoraj vidimo, da ga imajo tudi moduli. Tipom modulov pravimo signature. Signatura opisuje definirane tipe ter tipe definiranih vrednosti (ne pa njihovih implementacij). Signature pišemo podobno kot module, le da uporabimo blok sig ... end, tipe vrednosti pa podamo s ključno besedo val. Definicije tipov ostanejo enake.

Prvi namen signatur je specifikacija vsebine modula. Običajno delo začnemo tako, da v signaturi opišemo, kaj bodo sestavni deli modula, nato pa začnemo pisati implementacijo, ki ji zadošča. Ko definiramo modul, lahko zraven z označbo podamo tudi njegovo signaturo.

Če kakšna od naštetih funkcij manjka, bo OCaml to opazil in javil napako. Podobno bo preveril, ali se pri vseh definicijah ujemajo tipi.

**13\. Katere dele implementacije lahko skrivamo prek signatur in zakaj bi to želeli?**

Če uporabljamo pomožno funkcijo, ki ni del signature, navzven ne bo vidna. Skrivanje implementacij uporabnikom poenostavi uporabo, saj izpostavi le ključne funkcije. Hkrati pa razvijalcem olajša kasnejše spremembe implementacije, če na primer najdejo boljši algoritem. Če pomožne funkcije ne bi bile skrite, bi se lahko nanje kdo zanašal, kar bi otežilo kasnejše spremembe.

**14\. Kaj je Curry-Howardov izomorfizem? Kako lahko dokaze logičnih izjav prevajamo na obstoj funkcij?**

Curry-Howardov izomorfizem je povezava med logiko in računalništvom, ki pravi, da lahko vsako logično izjavo razumemo kot tip v programskem jeziku, njen dokaz pa kot vrednost tega tipa (na primer funkcijo).

Konkretno:
Logično konjunkcijo (in) predstavlja par (produktni tip).
Disjunkcijo (ali) predstavlja vsotni tip (npr. Left | Right).
Implikacijo (če – potem) predstavlja funkcijski tip.
Neresnico (⊥) predstavlja prazen tip (brez vrednosti), resnico pa enotski tip z eno vrednostjo.
Negacija ¬P je kar funkcija P -> ⊥ (če bi imeli P, bi dobili protislovje).
Dokaz izjave, na primer (P ∧ Q ⇒ R) ⇒ (P ⇒ (Q ⇒ R)), je tako navadna funkcija v OCamlu (natančneje funkcija curry). Ko OCaml preveri, da ima funkcija pravilen tip, s tem hkrati preveri tudi pravilnost logičnega dokaza. Na tem izomorfizmu temeljijo sodobni dokazovalniki, kot sta Lean ali Rocq.

**15\. V čem se dokazovanje v dokazovalniku kot je Lean, razlikuje od programiranja v jeziku kot je OCaml?**

Glavna razlika je, da je Lean specializiran za varno dokazovanje, medtem ko je OCaml splošni programski jezik.

Ključne razlike:
Rekurzija: OCaml dovoljuje neomejeno rekurzijo (vodi v cikle), Lean pa zahteva, da se funkcije zagotovo ustavijo (strukturna rekurzija).
Ločitev logike: Lean loči med Type (podatki) in Prop (logične izjave). Dokazi v Prop se ob izvajanju pobrišejo – to omogoča uporabo aksiomov (npr. izključene tretje možnosti), ki v OCamlu niso konstruktivno izvedljivi.
Pisanje dokazov: V OCamlu pišemo dokaze neposredno kot funkcije (nerodno pri kompleksnih izjavah), Lean pa omogoča taktike – ukaze (npr. intro, constructor), ki interaktivno gradijo dokaz in so bolj pregledni.
Bistvo: Lean gradi na Curry-Howardu, vendar doda varnost (ustavljivost) in praktičnost (taktike, brisanje dokazov), kar ga naredi za pravi dokazovalnik, ne le programski jezik.

**16\. Na primeru vektorjev razložite, kaj so odvisni tipi. Naštejte primere vrednosti/tipov odvisnih od vrednosti/tipov.**

Odvisni tipi so tipi, ki se spreminjajo glede na vrednost (ne le glede na drug tip). To omogoča izražanje predikatov in kvantifikatorjev v Curry-Howardovi korespondenci, s čimer presežemo izjavni račun.

Primer vektorjev (seznami z dolžino):
Navaden seznam nima informacije o dolžini v tipu. Vektor pa je seznam, katerega tip vključuje dolžino:
- `Vektor 0` je tip praznih seznamov.
- `Vektor 42` je tip seznamov z natanko 42 elementi.

Definicija v Leanu:
inductive Vektor : Nat → Type where
  | prazen : Vektor Nat.zero
  | sestavljen {n : Nat} : Int → Vektor n → Vektor (Nat.succ n)

Ko stikamo dva vektorja, mora biti to razvidno tudi v tipu:
def stakniVektor {m n : Nat} : Vektor m → Vektor n → Vektor (n + m)
Če bi se zmotili in vrnili napačno dolžino, bi Lean javil napako pri preverjanju tipov.

**17\. Čemu odvisni tipi ustrezajo v Curry-Howardovem izomorfizmu?**

V Curry-Howardovem izomorfizmu odvisni tipi ustrezajo kvantifikatorjem v predikatnem računu. Univerzalnemu kvantifikatorju ∀x : A, P(x) ustreza odvisni produktni tip Π x : A, B x, 
eksistenčnemu kvantifikatorju ∃x : A, P(x) pa odvisni vsotni tip Σ x : A, B x. Tako odvisni tipi razširijo izomorfizem iz izjavnega na predikatni račun.

**18\. Kakšni sta videti načeli indukcije na verižnih seznamih in dvojiških drevesih? Uporabite enega od njih na primeru.**

P([]) ∧ (∀ z, zs. P(zs) ⇒ P(z :: zs))
P(Prazno) ∧ (∀ l, x, d. P(l) ∧ P(d) ⇒ P(Sest (l, x, d))) ⟹ ∀ t. P(t)

**19\. Kako uporabljamo indukcijo ob prisotnosti pomožnih rekurzivnih funkcij?**



**20\. Kako deluje Turingov stroj?**

Turingov stroj je sestavljen iz končne množice simbolov, praznega simbola, končne množice stanj, začetnega stanja in prehodne funkcije. Delovanje poglej na spletni strani: množica trakov, konfiguracija stroja, delna funkcije step, run in eval.

**21\. Kaj so izračunljive funkcije in kaj trdi Church-Turingova teza?**

Funkcija f je izračunljiva natanko tedaj, kadar obstaja Turingov stroj M, da je f = eval_M.

Church-Turingova teza trdi, da je vsaka funkcija, ki jo lahko izračunamo z efektivnim postopkom (algoritmom), tudi izračunljiva s Turingovim strojem

**22\. Kaj je univerzalni Turingov stroj?**

Univerzalni Turingov stroj (UTS) je Turingov stroj, ki lahko simulira delovanje katerega koli drugega Turingovega stroja.

Natančneje: če neki Turingov stroj M kodiraš v število k_M  (njegovo "programsko kodo"), potem univerzalni stroj U s podatkoma (k_M, n) počne točno to, kar bi počel M, če ga zaženeš na vhodu n: eval_U(k_M, n) ≃ eval_M(n)

**23\. Kaj je ustavitveni orakelj in zakaj ne obstaja?**

Ne obstaja Turingov stroj H, da bi za vsak Turingov stroj M veljalo eval_H(k_M, n) = 0, če se M pri n ne ustavi
                 1, če se M pri n ustavi

Ustavitveni problem je vprašanje: ali obstaja Turingov stroj H, ki za poljuben stroj M in vhod n odloči, ali se M ustavi?
Ustavitveni problem je nerešljiv – takšen stroj H ne obstaja.
Ustavitveni problem je prvi in najbolj znan primer neodločljivega problema – problema, ki ga algoritmično ne moremo rešiti za vse možne vhode. To je temeljna omejitev računalništva: ne moremo avtomatsko preveriti, ali se bo poljuben program ustavil.

**24\. Kaj je razlika med spremenljivimi in nespremenljivimi podatkovnimi strukturami? Kdaj uporabimo katere?**

Temeljna razlika med obema vrstama podatkovnih struktur je v tem, kako obravnavata spremembe. **Nespremenljive podatkovne strukture** (kot so OCamlovi seznami) ob vsaki "spremembi" ne spremenijo obstoječe strukture, temveč ustvarijo **povsem novo** – prvotna ostane nespremenjena. Na primer, dodajanje elementa na začetek seznama naredi nov seznam, ki ima stari seznam za rep. **Spremenljive podatkovne strukture** (kot so OCamlove tabele `array`, reference ali Pythonovi seznami) pa omogočajo dejansko spreminjanje podatkov **na mestu** (v pomnilniku), pri čemer se struktura fizično spremeni.

Ključna posledica te razlike je **način predstavitve v pomnilniku**, kar vodi v različne **računske zahtevnosti** (časovne in prostorske) za posamezne operacije:
- **Nespremenljivi seznami** (`list`): dostop do naključnega elementa (`n–ti` element) zahteva `O(n)` časa (hoja po kazalcih), dodajanje na začetek je `O(1)`, izračun dolžine pa `O(n)` (razen če si dolžino sproti zapomnimo). So optimalni, kadar pogosto dodajamo na začetek in kadar želimo varno deliti podatke brez stranskih učinkov.
- **Spremenljive tabele** (`array`): indeksiranje in spreminjanje elementa sta `O(1)`, dodajanje na konec ali na začetek je `O(n)` (potrebno je premikanje elementov). Zato so tabele primerne, kadar pogosto dostopamo do elementov po indeksu ali kadar želimo podatke urejati na mestu (npr. Fisher-Yatesov algoritem za premešanje, urejanje z izbiranjem, mehurčki ali vstavljanjem).

**Kdaj uporabimo katere?**
- **Nespremenljive strukture (sezname)** uporabimo, ko želimo **varnost** (odsotnost stranskih učinkov), **enostavno sklepanje o programu** in kadar so spremembe redke ali potekajo z dodajanjem/odvzemanjem na začetku.
- **Spremenljive strukture (tabele, reference)** uporabimo, ko potrebujemo **učinkovitost** (predvsem naključen dostop), **fizično spreminjanje podatkov na mestu** (npr. hitro urejanje, premešanje) ali ko želimo simulirati običajne imperativne podatkovne strukture.

V praksi pogosto kombiniramo oba pristopa: na primer, za premešanje seznama ga pretvorimo v tabelo (`Array.of_list`), jo premešamo (`fisher_yates`) in nato morebiti vrnemo nazaj v seznam – s tem združimo prednosti nespremenljivosti za večino programa in učinkovitost spremenljivosti tam, kjer je to potrebno.

**25\. Kako je definirana notacija velikega O?**

**Notacija velikega O** se uporablja za **opisovanje zgornje meje rasti funkcije**, ko gre argument proti neskončnosti. Formalno: Pravimo, da je \(f(n) = O(g(n))\), če obstajata pozitivni konstanti \(c\) in \(n_0\), tako da za vse \(n \ge n_0\) velja \(|f(n)| \le c \cdot |g(n)|\).

V kontekstu računske zahtevnosti to pomeni: če algoritem porabi največ \(f(n)\) operacij pri vhodu velikosti \(n\), zapišemo, da je njegova časovna zahtevnost \(O(g(n))\), pri čemer \(g(n)\) poenostavi izraz tako, da upošteva le **najhitreje rastoči člen** in **izpusti konstante**. Na primer:
- \(O(3n^2 + 5n + 2)\) poenostavimo v \(O(n^2)\)
- \(O(2n + 8)\) poenostavimo v \(O(n)\)
- \(O(5)\) (konstanta) poenostavimo v \(O(1)\)

Tako notacija velikega O **pove, kako hitro narašča potreben čas/prostor z velikostjo vhoda**, ne da bi se spuščali v podrobnosti strojne izvedbe ali natančne konstante. Omogoča nam torej **primerjavo učinkovitosti algoritmov** na abstraktni ravni.

**26\. Kako so v pomnilniku predstavitvljeni verižni seznami in kako tabele?**

**Verižni seznami (OCaml `list`)** so v pomnilniku predstavljeni kot **veriga vozlišč** (celic). Vsaka celica hrani glavo (podatek) in kazalec (referenco) na naslednje vozlišče. Prazen seznam predstavlja posebna vrednost. V pomnilniškem zapisu so vozlišča lahko raztresena (povezana s kazalci), za dostop do `n`-tega elementa pa moramo slediti kazalcem od začetka – kar potrebuje `O(n)` korakov.

**Tabele (OCaml `array`, Python `list`)** so v pomnilniku predstavljene kot **zaporedni bloki** (tabela, kontiguiran kos pomnilnika). Elementi ležijo drug za drugim. Za tabelo je znana njena dolžina. Dostop do elementa po indeksu je stalen (`O(1)`) – izračunamo odmik (indeks × velikost elementa) in naslov. Pythonovi seznami so sicer dinamični (lahko jih razširjamo), a še vedno temeljijo na tabeli: hranijo podatek o velikosti, rezerviranem prostoru in referencah na objekte (saj so dinamično tipizirani). Na splošno pa tako OCamlove kot Pythonove tabele omogočajo hiter dostop po indeksu, medtem ko je dodajanje elementa na začetek ali v sredino počasno (zahteva premikanje drugih elementov).

**27\. Zakaj pri Pythonu objekti v pomnilniku vsebujejo tudi informacijo o tipu?**

Pythonovi objekti v pomnilniku vsebujejo informacijo o tipu, ker je Python **dinamično tipiziran jezik**. To pomeni, da se tipi spremenljivk preverjajo **šele med izvajanjem** programa, ne pa pred njim (kot v statično tipiziranem OCamlu).

Ker ima lahko ista spremenljivka v različnih delih programa objekte različnih tipov, mora Python ob vsakem dostopu do objekta **vedeti, za kakšen tip gre** – npr. ali gre za celo število, niz, seznam ali kaj drugega. Ta informacija je shranjena **skupaj z objektom v pomnilniku** (kot del glave objekta) in omogoča:
- pravilno interpretacijo podatkov (npr. kako prebrati vrednost),
- dinamično pošiljanje metod (npr. kaj naredi `+` glede na tip),
- preverjanje tipov med izvajanjem (npr. `type(x)` ali `isinstance`).

Informacija o tipu je potrebna tudi za **upravljanje pomnilnika** (npr. garbage collector) in za **debugiranje**.

Za primerjavo: v statično tipiziranem OCamlu (ali C-ju) informacije o tipu v pomnilniku **ni** – tip vsake vrednosti je znan že ob prevajanju in je "vkompiliran" v kodo, zato je objekt v pomnilniku zgolj gol podatek (npr. celo število zavzame 4 ali 8 bajtov brez dodatnih oznak). To prihrani prostor in čas, a zahteva, da tipi ostanejo nespremenljivi.

**28\.Kakšne so časovne zahtevnosti osnovnih operacij na verižnih seznamih in tabelah?**

| Operacija | Verižni seznam (OCaml `list`) | Tabela (OCaml `array`, Python `list`) |
|-----------|-------------------------------|----------------------------------------|
| **Indeksiranje** (dostop do i-tega elementa) | `O(n)` | `O(1)` |
| **Dodajanje na začetek** | `O(1)` | `O(n)` |
| **Dodajanje na konec** | `O(n)` | `O(1)`* |
| **Izračun dolžine** | `O(n)` | `O(1)` |
| **Izračun repa** (vsi elementi razen prvega) | `O(1)` | `O(n)` |

*Pri Pythonovih seznamih je dodajanje na konec (`append`) v povprečju `O(1)`, čeprav lahko občasno pride do podražitve zaradi razširjanja tabele (amortizirana analiza). Pri OCamlovih tabelah je dodajanje na konec (če tabelo ročno razširjamo) prav tako `O(n)`, saj je tabela fiksne velikosti.

**Povzetek:** Verižni seznami so učinkoviti pri operacijah na začetku (dodajanje, rep), tabele pa pri naključnem dostopu (indeksiranje) in dodajanju na konec.

**29\. Kako so definirana iskalna drevesa, kako potekajo na njih osnovne operacije in kakšna je njihova časovna zahtevnost?**

Iskalna drevesa so binarna drevesa, kjer so vsi elementi levega otroka manjši od korena, vsi elementi desnega otroka večji od korena in oba otroka sta tudi iskalni drevesi. Ta struktura poenostavi iskanje, dodajanje in brisanje elementov. 
Ni nam treba preiskati vseh elementov v drevesu, temveč največ toliko, kolikor je drevo globoko. Operacije imajo časovno zahtevnost O(h), kjer je h globina drevesa, lahko tudi O(n) pri neuravnoteženih drevesih.

**30\. Kako so definirana AVL drevesa, kako potekajo na njih osnovne operacije in kakšna je njihova časovna zahtevnost?**

Časovna zahtevnost teh dreves bo O(log n). AVL dreseva so iskalna drevesa, kjer je razlika višin otrok največ 1 in sta oba otroka tudi AVL drevesi. 
Pri osnovnih operacijah bo kdaj potrebno opraviti rotacijo, saj bo pri brisanju/dodajanju elementov prišlo razlike višin. Te rotacije imajo računsko zahtevnost O(1) (samo kazalce spremenimo).

**31\. Razložite algoritem hitrega potenciranja.**

let rec potenciraj a =
  function
  | 0 -> 1
  | n ->
      let k = potenciraj a (n / 2) in
      if n mod 2 = 0 then k * k else a * k * k

Opomba: fibonaccijeva števila

**32\. Kaj počne Fisher-Yatesov algoritem? Dokažite njegovo pravilnost.**

Fisher-Yatesov algoritem uporabimo, kadar želimo premešati tabelo. Deluje tako, da postopoma gradi naključno permutacijo prvotnega seznama. Najprej izmed vseh elementov izbere enega za prvo mesto, nato izmed vseh preostalih izbere naslednjega za drugo mesto in tako naprej. Pri tem algoritem vsa števila vodi v eni sami spreminjajoči se tabeli: v levi polovici (do vključno i-tega elementa) so že delno premešani elementi, v desni polovici (od i-tega do zadnjega) pa so še neizbrani elementi. V i-tem koraku izmed vseh neizbranih elementov naključno izberemo enega in ga zamenjamo z i-tim elementom. Algoritem v OCamlu napišemo kot:

let fisher_yates tabela =
  let n = Array.length tabela in
  for i = 0 to n - 2 do
    let j = i + Random.int (n - i) in
    zamenjaj tabela i j
  done

Poglejmo si še učinkovitost algoritma. Naredimo O(n) korakov, na vsakem pa zamenjamo dva elementa, kar lahko storimo v konstantnem času. Skupaj je časovna zahtevnost algoritma enaka O(n). Hitreje kot to ne gre, saj v manj kot n korakih ne moremo ustvariti permutacije n elementov. V nasprotnem primeru bi obstajal element, ki ga v nobenem koraku nismo izbrali, kar pomeni, da nekaterih permutacij ne bi mogli ustvariti.

**33\. Kako delujejo algoritmi za urejanje z izbiranjem, z vstavljanjem in z mehurčki.**

Omenjeni algoritmi delujejo v času O(n^2).

Urejanje z izbiranjem: deluje tako, da postopoma izbere najmanjši element in ga postavi na prvo mesto, nato izbere naslednji najmanjši element in ga postavi na drugo mesto, in tako naprej.

Urejanje z mehurčki: deluje tako, da postopoma zamenjuje pare zaporednih elementov, ki so v napačnem vrstnem redu. Če se na tak način postopoma sprehodimo čez vse pare v tabeli, bo največji element priplaval na zadnje mesto. Postopek ponovimo na preostalih manjših elementih, s čimer na predzadnje mesto priplava drugi največji element, in tako naprej. V zanko lahko dodamo še pogoj, da se zanka prekine, če v obhodu ni bilo nobenih zamenjav, saj to pomeni, da je tabela že urejena.

Urejanje z vstavljanjem: deluje tako, kot urejamo karte pri taroku (za tiste, ki jih urejamo). V roki imamo urejene karte in vsakič, ko dobimo novo, jo postavimo na pravo mesto. Pri urejanju tabel nimamo dveh tabel, temveč eno samo, v kateri na levi strani postopoma gradimo urejeni del, na desni pa so še nerazporejeni elementi.

**34\. Kako poteka urejanje z zlivanjem in kakšna je njegova časovna zahtevnost?**

Urejanje z zlivanjem deluje tako, da seznam razdelimo na dva manjša podseznama (vseeno kakšna, le da vsak vsebuje približno polovico elementov prvotnega seznama), nato pa vsakega rekurzivno uredimo. Ko sta obe polovici urejeni, ju lahko zlijemo tako, da z njunih začetkov postopoma jemljemo najmanjše še ne vzete elemente.
V OCamlu lahko delitev na pol najenostavneje izvedemo tako, da damo v eno polovico elemente na lihih, v drugo pa elemente na sodih mestih.
Zlivanje naredimo tako, da primerjamo glavi dveh seznamov, izberemo manjšo ter nadaljujemo rekurzivno. Ko je eden izmed seznamov prazen, vzamemo preostale elemente drugega seznama:
Njegova časovna zahtevnost je O(n log n).

**35\. Kako poteka hitro urejanje in kakšni sta njegova povprečna in najslabša časovna zahtevnost?**

Hitro urejanje deluje tako, da seznam razdeli na dva manjša podseznama, vsakega rekurzivno uredi, na koncu pa obe urejeni polovici združi. Razlika je v tem, da več dela opravi pri deljenju seznama na dva dela. Pri tem elemente uredi tako, da so v eni polovici manjši, v drugi polovici pa večji elementi. Posledica tega je, da je združevanje enostavno, saj obe polovici samo še staknemo. Elemente razdelimo po velikosti glede na izbrani element, ki mu pravimo pivot in ga običajno vzamemo z začetka seznama. 
V OCamlu seznam enostavno pivotiramo s pomočjo funkcije List.partition, ki seznam razdeli na elemente, ki zadoščajo predikatu, in tiste, ki mu ne.
Povprečna računska zahtevnost znaša O(n log n), najslabša pa O(n^2), ko je seznam že skoraj urejen.

**36\. Kako poteka hitro urejanje na mestu?**



**37\. Kakšna je razlika med pristopoma deli in vladaj ter dinamično programiranje?**

Deli in vladaj: nalogo razdelimo na manjše podnaloge, podnaloge rekurzivno rešimo in dobljene rešitve združimo v rešitev prvote naloge

Dinamično programiranje: včasih se bodo podnaloge prekrivale, kar bomo izkoristili tako, da bomo vsako rešili le enkrat. Podvojevanju se lahko izognemo na dva načina. Prvi je memoizacija, pri kateri si računalnik samodejno shranjuje izračunane rezulate drugi pa je pristop od spodaj navzgor, v katerem rešitve pripravimo v ustreznem vrstnem redu. Takih vrstnih redov je lahko več, saj moramo poskrbeti le za to, da so vse podnaloge pravočasno rešene

**38\. Primerjajte pristopa od spodaj navzdol ter od zgoraj navzdol pri reševanju nalog z dinamičnim programiranjem. Kaj so prednosti katerega pristopa?**



**39\. Kako implementiramo memoizacijo?**



**40\. Kakšne so razlike med implementacijo memoizacije v dinamičnem jeziku, kot je Python, in v statičnem jeziku, kot je OCaml?**
