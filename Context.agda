{-# OPTIONS --rewriting #-}
module Context where
open import Level
open import Function hiding (_∋_;const)
open import Data.Unit
open import Data.Product
open import FibSetoid
open import Univ.HLevel

data Cx : Set₁
⟦_⟧C : Cx → Set₁
data Functor (Γ : Cx) (n : hLevel) (F : ⟦ Γ ⟧C → Type n) : Set₁
record Typeover (n : hLevel) (Γ : Cx) : Set₁
⟦_⟧T : ∀ {n Γ} → Typeover n Γ → ⟦ Γ ⟧C → Set
EQC : ∀ Γ → ⟦ Γ ⟧C → ⟦ Γ ⟧C → Set
EQC₂ : ∀ {Γ} {a₁ a₂ b₁ b₂ : ⟦ Γ ⟧C} → EQC Γ a₁ a₂ → EQC Γ b₁ b₂ → EQC Γ a₁ b₁ → EQC Γ a₂ b₂ → Set
CONTEXT : Cx → OneType (suc zero) zero zero
RefC : ∀ {Γ} (γ : ⟦ Γ ⟧C) → EQC Γ γ γ
RefC-cong : ∀ {Γ} {γ γ' : ⟦ Γ ⟧C} (γ* : EQC Γ γ γ') → EQC₂ (RefC γ) (RefC γ') γ* γ*
_∋_∼⟨_⟩_ : ∀ {n Γ} (T : Typeover n Γ) {γ γ'} → ⟦ T ⟧T γ → EQC Γ γ γ' → ⟦ T ⟧T γ' → Set

infix 75 _,,_
data Cx where
  ε : Cx
  _,,_ : ∀ {n} (Γ : Cx) → Typeover n Γ → Cx

CONTEXT Γ = record {
  graph = record {
    Vertex = ⟦ Γ ⟧C ;
    Path = EQC Γ ;
    ref = RefC };
  isOneType = record {
    Fill = λ γ* → EQC₂ (RefGraph.Square.north γ*) (RefGraph.Square.south γ*) (RefGraph.Square.west γ*) (RefGraph.Square.east γ*) }}

data Functor Γ n F where
  make-Functor : (∀ {γ γ'} (γ* : EQC Γ γ γ') → Eq (F γ) (F γ')) → Functor Γ n F

ap₂ : ∀ {Γ n F} → Functor Γ n F → ∀ {γ γ'} → EQC Γ γ γ' → Eq (F γ) (F γ')
ap₂ (make-Functor F-cong) = F-cong

postulate ap₂-ref : ∀ {Γ n F} (F-cong : Functor Γ n F) (γ : ⟦ Γ ⟧C) → ap₂ F-cong (RefC γ) ▷ Refn (F γ)
{-# REWRITE ap₂-ref #-}

data Functor₂ Γ n F (F-cong : Functor Γ n F) : Set₁ where
  make-Functor₂ : (∀ {γ₁ γ₁' γ₂ γ₂'} (γ₁* : EQC Γ γ₁ γ₁') (γ₂* : EQC Γ γ₂ γ₂') (γₑ : EQC Γ γ₁ γ₂) (γₑ' : EQC Γ γ₁' γ₂')
    (sq-fill : EQC₂ γ₁* γ₂* γₑ γₑ') → [ n ] ap₂ F-cong γ₁* ∼⟪ eqn-cong (ap₂ F-cong γₑ) (ap₂ F-cong γₑ') ⟫ ap₂ F-cong γ₂*) →
    Functor₂ Γ n F F-cong

ap₃ : ∀ {Γ n F F-cong} → Functor₂ Γ n F F-cong → ∀ {γ₁ γ₁' γ₂ γ₂'} (γ₁* : EQC Γ γ₁ γ₁') (γ₂* : EQC Γ γ₂ γ₂') (γₑ : EQC Γ γ₁ γ₂) (γₑ' : EQC Γ γ₁' γ₂')
    (sq-fill : EQC₂ γ₁* γ₂* γₑ γₑ') → [ n ] ap₂ F-cong γ₁* ∼⟪ eqn-cong (ap₂ F-cong γₑ) (ap₂ F-cong γₑ') ⟫ ap₂ F-cong γ₂*
ap₃ (make-Functor₂ F-cong₂) = F-cong₂

postulate ap₃-ref : ∀ {Γ n F F-cong} (F-cong₂ : Functor₂ Γ n F F-cong) {γ γ'} (γ* : EQC Γ γ γ') →
                    ap₃ F-cong₂ (RefC γ) (RefC γ') γ* γ* (RefC-cong γ*) ▷ Refn-cong {n} (ap₂ F-cong γ*)
{-# REWRITE ap₃-ref #-}

--TODO Refactor
record Typeover n Γ where
  field
    obj : ∀ (γ : ⟦ Γ ⟧C) → Type n
    obj-cong : Functor Γ n obj
    obj-cong₂ : Functor₂ Γ n obj obj-cong
    obj-cong₃ : ∀ {γ δ : OneType.Square (CONTEXT Γ)}
      {enw : EQC Γ (OneType.Square.nw (CONTEXT Γ) γ) (OneType.Square.nw (CONTEXT Γ) δ)}
      {ene : EQC Γ (OneType.Square.ne (CONTEXT Γ) γ) (OneType.Square.ne (CONTEXT Γ) δ)}
      {esw : EQC Γ (OneType.Square.sw (CONTEXT Γ) γ) (OneType.Square.sw (CONTEXT Γ) δ)}
      {ese : EQC Γ (OneType.Square.se (CONTEXT Γ) γ) (OneType.Square.se (CONTEXT Γ) δ)}
      {γsq : OneType.Fill (CONTEXT Γ) γ} {δsq : OneType.Fill (CONTEXT Γ) δ}
      {sq₁ : OneType.Fill (CONTEXT Γ) (record
                                         { nw = OneType.Square.nw (CONTEXT Γ) γ
                                         ; ne = OneType.Square.ne (CONTEXT Γ) γ
                                         ; sw = OneType.Square.nw (CONTEXT Γ) δ
                                         ; se = OneType.Square.ne (CONTEXT Γ) δ
                                         ; north = OneType.Square.north (CONTEXT Γ) γ
                                         ; south = OneType.Square.north (CONTEXT Γ) δ
                                         ; west = enw
                                         ; east = ene
                                         })}
      {sq₂ : OneType.Fill (CONTEXT Γ) (record
                                         { nw = _
                                         ; ne = _
                                         ; sw = _
                                         ; se = _
                                         ; north = OneType.Square.south (CONTEXT Γ) γ
                                         ; south = OneType.Square.south (CONTEXT Γ) δ
                                         ; west = esw
                                         ; east = ese
                                         })}
      {sqₑ : OneType.Fill (CONTEXT Γ) (record
                                         { nw = _
                                         ; ne = _
                                         ; sw = _
                                         ; se = _
                                         ; north = OneType.Square.west (CONTEXT Γ) γ
                                         ; south = OneType.Square.west (CONTEXT Γ) δ
                                         ; west = enw
                                         ; east = esw
                                         })}
      {sqₑ' : OneType.Fill (CONTEXT Γ) (record
                                          { nw = _
                                          ; ne = _
                                          ; sw = _
                                          ; se = _
                                          ; north = OneType.Square.east (CONTEXT Γ) γ
                                          ; south = OneType.Square.east (CONTEXT Γ) δ
                                          ; west = ene
                                          ; east = ese
                                          })} →
      [ pred n ] ap₃ obj-cong₂ _ _ _ _ γsq ∼⟪ eqTTn-cong n (ap₃ obj-cong₂ _ _ _ _ sq₁) (eqn-cong₂ n (ap₃ obj-cong₂ _ _ _ _ sqₑ) (ap₃ obj-cong₂ _ _ _ _ sqₑ')) (ap₃ obj-cong₂ _ _ _ _ sq₂) ⟫ ap₃ obj-cong₂ _ _ _ _ δsq

⟦ ε ⟧C = Lift ⊤
⟦ Γ ,, S ⟧C = Σ[ γ ∈ ⟦ Γ ⟧C ] ⟦ S ⟧T γ

⟦ A ⟧T γ = TT (Typeover.obj A γ)

EQC ε (lift tt) (lift tt) = ⊤
EQC (Γ ,, S) (γ , s) (γ' , s') = Σ[ γ* ∈ EQC Γ γ γ' ] S ∋ s ∼⟨ γ* ⟩ s'

T ∋ a ∼⟨ γ* ⟩ b = [ _ ] a ∼⟪ ap₂ (Typeover.obj-cong T) γ* ⟫ b

RefC {ε} γ = tt
RefC {Γ ,, T} (γ , t) = RefC γ , refn t

EQC₂ {ε} tt tt tt tt = ⊤
EQC₂ {_,,_ {n} Γ T} {a₁ , s₁} {a₂ , s₂} {b₁ , t₁} {b₂ , t₂} (a* , s*) (b* , t*) (e₁ , p₁) (e₂ , p₂) = 
  Σ[ sq ∈ EQC₂ {Γ} a* b* e₁ e₂ ] ([ _ ] s* ∼⟪ eqTTn-cong n p₁ (ap₃ (Typeover.obj-cong₂ T) _ _ _ _ sq) p₂ ⟫ t*)

RefC-cong {ε} _ = tt
RefC-cong {_,,_ {n} Γ T} (γ* , t*) = RefC-cong γ* , refn-cong {n} t*

weak : ∀ {Γ m n} {T : Typeover m Γ} → Typeover n Γ → Typeover n (Γ ,, T)
weak {T = T} S = record { 
  obj = λ {(γ , _) → Typeover.obj S γ};
  obj-cong = make-Functor λ {(γ* , _) → ap₂ (Typeover.obj-cong S) γ*};
  obj-cong₂ = make-Functor₂ λ {_ _ _ _ (γsq , _) → ap₃ (Typeover.obj-cong₂ S) _ _ _ _ γsq};
  obj-cong₃ = Typeover.obj-cong₃ S }

record Section {n Γ} (T : Typeover n Γ) : Set₁ where
  field
    vertex : ∀ (γ : ⟦ Γ ⟧C) → ⟦ T ⟧T γ
    edge   : ∀ {γ γ'} (γ* : EQC Γ γ γ') → T ∋ vertex γ ∼⟨ γ* ⟩ vertex γ'
    face   : ∀ {γ₁ γ₁' γ₂ γ₂'} {γ₁* : EQC Γ γ₁ γ₁'} {γ₂* : EQC Γ γ₂ γ₂'}
      {γₑ : EQC Γ γ₁ γ₂} {γₑ' : EQC Γ γ₁' γ₂'} (sq-fill : EQC₂ γ₁* γ₂* γₑ γₑ') →
      [ pred n ] edge γ₁* ∼⟪ eqTTn-cong n (edge γₑ) (ap₃ (Typeover.obj-cong₂ T) _ _ _ _ sq-fill) (edge γₑ') ⟫ edge γ₂*

infix 5 _∋_
data _∋_ : ∀ {n} (Γ : Cx) (T : Typeover n Γ) → Set₁ where
  top : ∀ {n Γ} {T : Typeover n Γ} → Γ ,, T  ∋ weak T
  pop : ∀ {m n Γ} {S : Typeover m Γ} {T : Typeover n Γ} → Γ ∋ T → Γ ,, S ∋ weak T

⟦_⟧∋ : ∀ {n Γ} {T : Typeover n Γ} → Γ ∋ T → (γ : ⟦ Γ ⟧C) → ⟦ T ⟧T γ
⟦ top ⟧∋ (_ , t) = t
⟦ pop i ⟧∋ (γ , _) = ⟦ i ⟧∋ γ

⟦_⟧∋-cong : ∀ {n Γ} {T : Typeover n Γ} (x : Γ ∋ T) {γ γ'} (γ* : EQC Γ γ γ') → T ∋ ⟦ x ⟧∋ γ ∼⟨ γ* ⟩ ⟦ x ⟧∋ γ'
⟦ top ⟧∋-cong (_ , t*) = t*
⟦ pop x ⟧∋-cong (γ* , _) = ⟦ x ⟧∋-cong γ*

⟦_⟧∋-cong₂ : ∀ {n Γ} {T : Typeover n Γ} (x : Γ ∋ T) {a₁ a₂ b₁ b₂} {a* : EQC Γ a₁ a₂} {b* : EQC Γ b₁ b₂} 
  {p₁ : EQC Γ a₁ b₁} {p₂ : EQC Γ a₂ b₂}
  (sq : EQC₂ {Γ} a* b* p₁ p₂) → 
  [ _ ] ⟦ x ⟧∋-cong a* ∼⟪ eqTTn-cong n (⟦ x ⟧∋-cong p₁) (ap₃ (Typeover.obj-cong₂ T) _ _ _ _ sq) (⟦ x ⟧∋-cong p₂) ⟫ ⟦ x ⟧∋-cong b*
⟦ top ⟧∋-cong₂ (_ , t₂) = t₂
⟦ pop x ⟧∋-cong₂ (γ₂ , _) = ⟦ x ⟧∋-cong₂ γ₂

⟦_⟧V : ∀ {n Γ} {T : Typeover n Γ} → (Γ ∋ T) → Section T
⟦ x ⟧V = record { vertex = ⟦ x ⟧∋ ; edge = ⟦ x ⟧∋-cong ; face = ⟦ x ⟧∋-cong₂ }

K : ∀ n Γ → Type n → Typeover n Γ
K n _ A = record { 
  obj = λ _ → A ; 
  obj-cong = make-Functor (λ _ → Refn A) ;
  obj-cong₂ = make-Functor₂ (λ _ _ _ _ _ → Refn-cong (Refn A)) ;
  obj-cong₃ = Refn-cong₂ {n} (Refn-cong (Refn A)) }

const : ∀ {n Γ} {A : Type n} (a : TT A) → Section (K n Γ A)
const {n} a = record {
  vertex = λ _ → a ;
  edge = λ _ → refn a ;
  face = λ _ → refn-cong {n} (refn a) }

EqTypeover : ∀ {n Γ} → Typeover n Γ → Typeover n Γ → Typeover n Γ
EqTypeover {n} S T = record {
  obj = λ γ → eqn (Typeover.obj S γ) (Typeover.obj T γ) ;
  obj-cong = make-Functor (λ γ* → eqn-cong (ap₂ (Typeover.obj-cong S) γ*) (ap₂ (Typeover.obj-cong T) γ*)) ;
  obj-cong₂ = make-Functor₂ (λ γ₁* γ₂* γₑ γₑ' sq-fill → eqn-cong₂ n (ap₃ (Typeover.obj-cong₂ S) _ _ _ _ sq-fill) (ap₃ (Typeover.obj-cong₂ T) _ _ _ _ sq-fill)) ;
  obj-cong₃ = λ {γ} {δ} {enw} {ene} {esw} {ese} {γsq} {δsq} {sq₁} {sq₂} {sqₑ}
                  {sqₑ'} →
                  eqn-cong₃ n (Typeover.obj-cong₃ S) (Typeover.obj-cong₃ T) }

EqT : ∀ {n Γ} (S T : Typeover n Γ) → Set₁
EqT S T = Section (EqTypeover S T)

EqTypeover-cong : ∀ {n Γ} {S S' T T' : Typeover n Γ} →
  EqT S S' → EqT T T' →
  EqT (EqTypeover S T) (EqTypeover S' T')
EqTypeover-cong {n} S* T* = record {
  vertex = λ γ → eqn-cong (Section.vertex S* γ) (Section.vertex T* γ) ;
  edge = λ γ* → eqn-cong₂ n (Section.edge S* γ*) (Section.edge T* γ*) ;
  face = λ sq-fill → eqn-cong₃ n (Section.face S* sq-fill) (Section.face T* sq-fill) }

refT : ∀ {n Γ} (T : Typeover n Γ) → EqT T T
refT {n} {Γ} T = record {
  vertex = λ γ → Refn (Typeover.obj T γ) ;
  edge = λ γ* → Refn-cong (ap₂ (Typeover.obj-cong T) γ*) ;
  face = λ sq-fill → Refn-cong₂ {n} (ap₃ (Typeover.obj-cong₂ T) _ _ _ _ sq-fill) }

eqS : ∀ {n Γ} {S T : Typeover n Γ} → Section S → EqT S T → Section T → Typeover (pred n) Γ
eqS {n} {Γ} {S} {T} s e t = record {
  obj = λ γ → eqTTn (Section.vertex s γ) (Section.vertex e γ) (Section.vertex t γ) ;
  obj-cong = make-Functor (λ γ* → eqTTn-cong n (Section.edge s γ*) (Section.edge e γ*) (Section.edge t γ*)) ;
  obj-cong₂ = make-Functor₂ (λ γ₁* γ₂* γₑ γₑ' sq-fill → eqTTn-cong₂ n (Section.face s sq-fill) (Section.face e sq-fill) (Section.face t sq-fill)) ;
  obj-cong₃ = trivial n }

--TODO Fill in
postulate eqS-cong : ∀ {n Γ}
                   {S S' T T' : Typeover n Γ}
                   {S* : EqT S S'} {T* : EqT T T'} {e : Section (EqTypeover S T)} {e' : Section (EqTypeover S' T')}
                   {s : Section S} {s' : Section S'} {t : Section T} {t' : Section T'} →
                   Section (eqS s S* s') → Section (eqS e (EqTypeover-cong {n} {_} {S} {S'} {T} {T'} S* T*) e') → Section (eqS t T* t') →
                   EqT (eqS s e t) (eqS s' e' t')

refS : ∀ {n Γ} {T : Typeover n Γ} (s : Section T) → Section (eqS s (refT T) s)
refS {n} {Γ} {T} s = record {
  vertex = λ γ → refn (Section.vertex s γ) ;
  edge = λ γ* → refn-cong {n} (Section.edge s γ*) ;
  face = λ _ → trivial n }

--TODO Inline
OneTypeMap : Cx → Cx → Set₁
OneTypeMap Γ Δ = OneTypeFunctor (CONTEXT Γ) (CONTEXT Δ)

record OneTypeMapEq {Γ Δ} (F G : OneTypeMap Γ Δ) : Set₁ where
  field
    vertex : ∀ γ → EQC Δ (app F γ) (app G γ)
    edge : ∀ {γ γ'} (γ* : EQC Γ γ γ') → EQC₂ (vertex γ) (vertex γ') (app₂ F γ*) (app₂ G γ*)

TypeoverF : ∀ {n} {Γ Δ} → OneTypeMap Γ Δ → Typeover n Δ → Typeover n Γ
TypeoverF F T = record {
  obj = λ γ → Typeover.obj T (app F γ) ;
  obj-cong = make-Functor (λ γ* → ap₂ (Typeover.obj-cong T) (app₂ F γ*)) ;
  obj-cong₂ = make-Functor₂ (λ γ₁* γ₂* γₑ γₑ' sq-fill → ap₃ (Typeover.obj-cong₂ T) (app₂ F γ₁*) (app₂ F γ₂*) (app₂ F γₑ) (app₂ F γₑ') (app₃ F sq-fill)) ;
  obj-cong₃ = Typeover.obj-cong₃ T}

Typeover-eq : ∀ {n Γ Δ ⟦ρ⟧ ⟦σ⟧} (T : Typeover n Δ) →
  OneTypeMapEq ⟦ρ⟧ ⟦σ⟧ →
  (F : Section (TypeoverF ⟦ρ⟧ T))
  (G : Section (TypeoverF ⟦σ⟧ T)) →
  Typeover (pred n) Γ
Typeover-eq {n} {⟦ρ⟧ = ⟦ρ⟧} {⟦σ⟧} T ⟦τ⟧ F G = record {
  obj = λ γ → eqTTn (Section.vertex F γ) (ap₂ (Typeover.obj-cong T) (OneTypeMapEq.vertex ⟦τ⟧ γ)) (Section.vertex G γ) ;
  obj-cong = make-Functor (λ {γ} {γ'} γ* → eqTTn-cong n (Section.edge F γ*) (ap₃ (Typeover.obj-cong₂ T) (OneTypeMapEq.vertex ⟦τ⟧ _) (OneTypeMapEq.vertex ⟦τ⟧ _) (app₂ ⟦ρ⟧ γ*) (app₂ ⟦σ⟧ γ*) (OneTypeMapEq.edge ⟦τ⟧ γ*)) (Section.edge G γ*)) ;
  obj-cong₂ = make-Functor₂ (λ γ₁* γ₂* γₑ γₑ' sq-fill → eqTTn-cong₂ n (Section.face F sq-fill) (Typeover.obj-cong₃ T) (Section.face G sq-fill)) ;
  obj-cong₃ = trivial n }
