set_option autoImplicit false

/------------------------------------------------------------------------------
 ## Naravna števila

 - Definirajte funkcijo, ki *rekurzivno* (torej naivno in ne direktno s formulo,
    ki jo boste morali dokazati) sešteje prvih `n` lihih naravnih števil, ter
    dokažite, da zanjo velja znana enakost.
 - Definirajte funkcijo, ki *rekurzivno* sešteje prvih `n` produktov dveh
    zaporednih naravnih števil, ter dokažite da zanjo velja znana enakost
    (najprej v obliki, ki ne zahteva deljenja, nato pa še v običajni obliki).

 Indukcijska koraka dokazov trditev `vsota_lihih_kvadrat` in `formula_produktov`
 dokažite z uporabo `calc` bloka.

 *Namig*: pri krajših manipulacijah numeričnih literalov nam taktika `rfl`
 pogosto zadostuje.
------------------------------------------------------------------------------/

-- Vsota prvih n lihih naravnih števil
def vsota_lihih : Nat → Nat :=
  fun n =>
    match n with
    | Nat.zero => Nat.zero
    | Nat.succ m => vsota_lihih m + (2 * m + 1)

theorem vsota_lihih_kvadrat : (n : Nat) → vsota_lihih n = n * n :=
  by
    intro n
    induction n with
    | zero =>
        simp [vsota_lihih]
    | succ m ih =>
        calc
          vsota_lihih (m + 1)
          _ = vsota_lihih m + (2 * m + 1) := by rw [vsota_lihih]
          _ = m * m + (2 * m + 1) := by rw [ih]
          _ = m * m + (m + m + 1) := by rw [Nat.two_mul]
          _ = m * m + m + m + 1 := by repeat rw [Nat.add_assoc]
          _ = m * m + m * 1 + 1 * m + 1 * 1 := by rw [Nat.one_mul, Nat.mul_one]
          _ = m * (m + 1) + 1 * m + 1 * 1 := by rw [← Nat.mul_add]
          _ = m * (m + 1) + 1 * (m + 1) := by rw [Nat.add_assoc, ← Nat.mul_add]
          _ = (m + 1) * (m + 1) := by rw [← Nat.add_mul]


-- Vsota prvih n produktov zaporednih naravnih števil
def vsota_produktov : Nat → Nat :=
  fun n =>
    match n with
    | Nat.zero => Nat.zero
    | Nat.succ m => vsota_produktov m + (m + 1) * (m + 2)

theorem formula_produktov : (n : Nat) → 3 * vsota_produktov n = n * (n + 1) * (n + 2) :=
  by
    intro n
    induction n with
    | zero =>
        simp [vsota_produktov]
    | succ m ih =>
        calc
          3 * vsota_produktov (m + 1)
          _ = 3 * (vsota_produktov m + (m + 1) * (m + 2)) := by rw [vsota_produktov]
          _ = 3 * vsota_produktov m + 3 * (m + 1) * (m + 2) := by rw [Nat.mul_add, Nat.mul_assoc]
          _ = m * (m + 1) * (m + 2) + 3 * (m + 1) * (m + 2) := by rw [ih]
          _ = (m + 1) * (m + 2) * m + 3 * (m + 1) * (m + 2) := by rw [Nat.mul_comm m (m+1), Nat.mul_assoc, Nat.mul_comm m (m+2), ← Nat.mul_assoc]
          _ = ((m + 1) * (m + 2)) * m + ((m + 1) * (m + 2)) * 3 := by rw [Nat.mul_comm 3 (m+1), Nat.mul_assoc (m+1) 3 (m+2), Nat.mul_comm 3 (m+2), ← Nat.mul_assoc]
          _ = ((m + 1) * (m + 2)) * (m + 3) := by rw [← Nat.mul_add]
          _ = (m + 1) * (m + 1 + 1) * (m + 1 + 2) := by rfl

theorem prava_formula_produktov : (n : Nat) → vsota_produktov n = (n * (n + 1) * (n + 2)) / 3 :=
  by
    intro n
    calc
      vsota_produktov n
      _ = vsota_produktov n * 3 / 3 := by omega
      _ = 3 * vsota_produktov n / 3 := by rw [Nat.mul_comm]
      _ = (n * (n + 1) * (n + 2)) / 3 := by simp [formula_produktov]

/------------------------------------------------------------------------------
 ## Vektorji

 Definirajmo vektorje z elementi poljubnega tipa. Za ustrezno delovanje
 zapišemo funkcijo stikanja dveh vektorjev s pomočjo taktik.

 Zapišite še funkcije:
 - `obrni`, ki vrne na vektor z elementi v obratnem vrstnem redu,
 - `preslikaj`, ki preslika vse elemente vektorja z dano funkcijo,
 - `zip`, ki združi dva vektorja v vektor parov,
 - `dolzina`, ki vrne dolžino vektorja,
 - `glava` in `rep`, ki varno vrneta glavo in rep *nepraznega* vektorja.
 Rezultati operacij na testnem vektorju `[1,2,3]` so zapisani ob koncu
 razdelka `Vektorji`.

 Dokažite tudi trditve o teh funkcijah:
 - `preslikaj_identiteto`: preslikava elementov vektorja z identiteto pusti
    vektor nespremenjen,
 - `preslikaj_kompozitum`: preslikava s kompozitumom funkcij je enaka
    kompozitumu preslikav s posameznimi funkcijami,
 - `dolzina_pravilna`: dolžina vektorja je enaka njegovi indeksirani dolžini,
 - `preslikaj_in_zip_se_ujemata`: preslikava elementov vektorja in nato
    združevanje z `zip` je enako združevanju z `zip` in nato preslikavi parov.
------------------------------------------------------------------------------/

inductive Vektor : Type → Nat → Type where
  | prazen : {A : Type} → Vektor A 0
  | sestavljen : {A : Type} → {n : Nat} → A → Vektor A n → Vektor A (n + 1)
deriving Repr

def stakni : {A : Type} → {m n : Nat} → Vektor A m → Vektor A n → Vektor A (m + n) :=
  fun xs ys => match xs with
  | .prazen =>
    by
      rw [Nat.add_comm]
      exact ys
  | .sestavljen x xs' =>
    by
      rw [Nat.add_right_comm]
      exact .sestavljen x (stakni xs' ys)

def obrni : {A : Type} → {m : Nat} → Vektor A m → Vektor A m :=
  fun xs => match xs with
  | .prazen => .prazen
  | .sestavljen x xs' => stakni (obrni xs') (.sestavljen x .prazen)


def preslikaj : {A B : Type} → {n : Nat} → (A → B) → Vektor A n → Vektor B n :=
  fun f xs => match xs with
  | .prazen => .prazen
  | .sestavljen x xs' => .sestavljen (f x) (preslikaj f xs')


def zip : {A B : Type} → {n : Nat} → Vektor A n → Vektor B n → Vektor (A × B) n :=
  fun xs ys => match xs with
  | .prazen => .prazen
  | .sestavljen x xs' => match ys with
                        | .sestavljen y ys' => .sestavljen (x, y) (zip xs' ys')

def dolzina : {A : Type} → {n : Nat} → Vektor A n → Nat :=
  fun xs => match xs with
  | .prazen => 0
  | .sestavljen _ xs' => 1 + dolzina xs'

def glava : {A : Type} → {n : Nat} → Vektor A (n+1) → A :=
  fun xs => match xs with
  | .sestavljen x _ => x

def rep {A : Type} {n : Nat} : Vektor A (n+1) → Vektor A n :=
  fun xs => match xs with
  | .sestavljen _ xs' => xs'

theorem preslikaj_identiteto : {A : Type} → {n : Nat} → (xs : Vektor A n) →
  preslikaj id xs = xs :=
  by
    intro A n xs
    induction xs with
    | prazen =>
      simp [preslikaj]
    | sestavljen x xs' ih =>
      simp [preslikaj, ih]

theorem preslikaj_kompozitum :
  {A B C : Type} → {n : Nat} → (f : A → B) → (g : B → C) → (xs : Vektor A n) →
  preslikaj (fun x => g (f x)) xs = preslikaj g (preslikaj f xs) :=
  by
    intro A B C n f g xs
    induction xs with
    | prazen =>
      simp [preslikaj]
    | sestavljen x xs' ih =>
      simp [preslikaj, ih]

theorem dolzina_pravilna : {A : Type} → {n : Nat} → (xs : Vektor A n) →
  dolzina xs = n :=
  by
    intro A n xs
    induction xs with
    | prazen =>
      simp [dolzina]
    | sestavljen x xs' ih =>
      simp [dolzina, ih]
      omega

theorem preslikaj_in_zip_se_ujemata : {A B C : Type} → {n : Nat} →
  (f : A → B) → (g : A → C) → (xs : Vektor A n) →
  zip (preslikaj f xs) (preslikaj g xs) = preslikaj (fun x => (f x, g x)) xs :=
  by
    intro A B C n f g xs
    induction xs with
    | prazen =>
      simp [preslikaj, zip]
    | sestavljen x xs' ih =>
      simp [preslikaj, zip, ih]

-- Primeri rezultatov operacij
def primer_vektorja : Vektor Nat 3 :=
  .sestavljen 1 (.sestavljen 2 (.sestavljen 3 .prazen))

#eval obrni primer_vektorja
-- Vrne: Vektor.sestavljen 3 (Vektor.sestavljen 2 (Vektor.sestavljen 1 (Vektor.prazen)))
#eval preslikaj (fun x => x + 10) primer_vektorja
-- Vrne: Vektor.sestavljen 11 (Vektor.sestavljen 12 (Vektor.sestavljen 13 (Vektor.prazen)))
#eval zip primer_vektorja primer_vektorja
-- Vrne: Vektor.sestavljen (1, 1) (Vektor.sestavljen (2, 2) (Vektor.sestavljen (3, 3) (Vektor.prazen)))
#eval dolzina primer_vektorja
-- Vrne: 3
#eval glava primer_vektorja
-- Vrne: 1
#eval rep primer_vektorja
-- Vrne: Vektor.sestavljen 2 (Vektor.sestavljen 3 (Vektor.prazen))

/------------------------------------------------------------------------------
 ## Logične izjave in predikatni račun

 Dokažite spodnje logične trditve.

 Dokazati morate 3 izjave brez predikatov in 3 izjave s predikatoma `forall`
 in `exists`. Zadnja je _paradoks pivca_, ki pravi:
   "V vsaki neprazni gostilni obstaja gost, za katerega velja,
   da če pije on, pijejo vsi v gostilni."

 Pri nekaterih dokazih boste potrebovali dokaze klasične logike iz modula
 `Classical`.
------------------------------------------------------------------------------/

theorem dvojna_negacija {P : Prop} : ¬¬P ↔ P :=
  by
    apply Iff.intro
    · intro h
      apply Classical.byContradiction
      intro h1
      contradiction
    · intro h
      intro h1
      contradiction


theorem trojna_negacija {P : Prop} : ¬¬¬P ↔ ¬P :=
  by
    apply Iff.intro
    · intro h
      apply Classical.byContradiction
      intro h1
      contradiction
    · intro h
      intro h1
      contradiction

theorem kontrapozitivna_oblika {P Q : Prop} : (P → Q) ↔ (¬Q → ¬P) :=
  by
    apply Iff.intro
    · intro hpq
      intro hnq
      intro hp
      exact hnq (hpq hp)
    · intro hnqnp
      intro hp
      apply Classical.byContradiction
      intro hnq
      have hnp : ¬P := hnqnp hnq
      contradiction


theorem pravilo_obstaja_disjunkcija : {A : Type} → {P Q : A → Prop} →
  (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) :=
  by
    intro A P Q
    apply Iff.intro
    · intro h
      rcases h with ⟨x, hx⟩
      cases hx with
      | inl hp =>
        left
        exact ⟨x, hp⟩
      | inr hq =>
        right
        exact ⟨x, hq⟩

    · intro h
      cases h with
      | inl hpx =>
        rcases hpx with ⟨x, hP⟩
        exact ⟨x, Or.inl hP⟩
      | inr hqx =>
        rcases hqx with ⟨x, hQ⟩
        exact ⟨x, Or.inr hQ⟩


theorem obstaja_p_ali_za_vse_ne_p {A : Type} {P : A → Prop} :
  (∃ x, P x) ∨ (∀ x, ¬ P x) :=
  by
    have h := Classical.em (∃ x, P x)
    cases h with
    | inl h1 =>
      left
      exact h1
    | inr h2 =>
      right
      intro x
      intro hpx
      have : ∃ x, P x := ⟨x, hpx⟩
      exact h2 this


theorem paradoks_pivca :
  {G : Type} → {P : G → Prop} →
  (g : G) →  -- (g : G) pove, da je v gostilni vsaj en gost
  ∃ (p : G), (P p → ∀ (x : G), P x) :=
  by
    intro G P g
    have h := Classical.em (∀ (x : G), P x)
    cases h with -- ločimo primeri, ko pijejo vsi in ko ne pijejo vsi
    | inl h_vsi =>
      exact ⟨g, fun _ => h_vsi⟩ -- če pijejo vsi, potem je očitno
    | inr h_ne_vsi =>
      have h_obstaja : ∃ (x : G), ¬P x := by -- če ne pijejo vsi, potem obstaja nekdo, ki ne pije
        apply Classical.byContradiction
        intro h_neobstaja
        apply h_ne_vsi
        intro x
        apply Classical.byContradiction
        intro h_nepije
        apply h_neobstaja
        exact ⟨x, h_nepije⟩
      rcases h_obstaja with ⟨p, hp⟩
      exact ⟨p, fun _ => by contradiction⟩


/------------------------------------------------------------------------------
 ## Dvojiška drevesa

  Podan je tip dvojiških dreves skupaj s funkcijami za zrcaljenje drevesa,
  izračun višine in velikosti drevesa.
  Dokažite trditvi:
 - `zrcaljenje_ohrani_visino`: zrcaljenje drevesa ohrani njegovo višino,
 - `visina_manjsa_ali_enaka_velikosti`: višina drevesa je vedno manjša ali
    enaka njegovi velikosti.

  V drugem delu sta definirani funkciji `vsota` in `vsota'`, ki izračunata
  vsoto vseh elementov v drevesu z naravnimi števili. Prva jo izračuna naivno,
  druga pa z uporabo pomožne funkcije z akumulatorjem. Dokažite, da obe funkciji
  dajeta enak rezultat za vsako drevo z naravnimi števili.
  Do pomožne funkcije `aux` lahko dostopate kot `vsota'.aux`.
-------------------------------------------------------------------------------/

inductive Drevo : Type → Type where
  | prazno : {A : Type} → Drevo A
  | sestavljeno : {A : Type} → A → Drevo A → Drevo A → Drevo A

def visina : {A : Type} → Drevo A → Nat :=
  fun t => match t with
  | .prazno => 0
  | .sestavljeno _ l d => 1 + max (visina l) (visina d)

def zrcali : {A : Type} → Drevo A → Drevo A :=
  fun t => match t with
  | .prazno => .prazno
  | .sestavljeno x l d => .sestavljeno x (zrcali d) (zrcali l)

def velikost : {A : Type} → Drevo A → Nat :=
  fun t => match t with
  | .prazno => 0
  | .sestavljeno _ l d => 1 + velikost l + velikost d

theorem zrcaljenje_ohrani_visino :
  {A : Type} → (t : Drevo A) →
  visina (zrcali t) = visina t :=
  by
    intro A t
    induction t with
    | prazno =>
      simp [zrcali]
    | sestavljeno x l d ihl ihd =>
      simp [zrcali, visina, ihl, ihd, Nat.max_comm]

theorem visina_manjsa_ali_enaka_velikosti :
  {A : Type} → (t : Drevo A) →
  visina t ≤ velikost t :=
  by
    intro A t
    induction t with
    | prazno =>
      simp [visina]
    | sestavljeno x l d ihl ihd =>
      simp [visina, velikost]
      omega

-- Drugi del
def vsota : Drevo Nat → Nat :=
  fun t => match t with
  | .prazno => 0
  | .sestavljeno x l d => x + vsota l + vsota d

def vsota' : Drevo Nat → Nat :=
  let rec aux : Drevo Nat → Nat → Nat :=
    fun t acc => match t with
    | .prazno => acc
    | .sestavljeno x l d => aux l (x + aux d acc)
  fun t => aux t 0

theorem pomozna : ∀ t acc, vsota'.aux t acc = vsota t + acc :=
  by
    intro t
    induction t with
    | prazno =>
      intro acc
      simp [vsota, vsota'.aux]
    | sestavljeno x l d ihl ihd =>
      intro acc
      simp [vsota'.aux, vsota]
      rw [ihl]
      rw [ihd]
      omega



theorem vsota_eq_vsota' : ∀ {t : Drevo Nat}, vsota t = vsota' t :=
  by
    intro t
    simp [vsota', pomozna]
