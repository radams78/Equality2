\begin{code}
{-# OPTIONS --rewriting #-}
module Context where
open import Level
open import Function hiding (_∋_;const)
open import Data.Unit
open import Data.Product
open import Semantics.RefGraph
open import Semantics.TwoGraph
open import Univ.HLevel
\end{code}

%<*Cx>
\begin{code}
data Cx : Set₁
\end{code}
%</Cx>

%<*IntC>
\begin{code}
⟦_⟧C : Cx → Set₁
\end{code}
%</IntC>

\begin{code}
data Functor (Γ : Cx) (n : hLevel) (F : ⟦ Γ ⟧C → Type n) : Set₁
record Typeover (n : hLevel) (Γ : Cx) : Set₁
⟦_⟧T : ∀ {n Γ} → Typeover n Γ → ⟦ Γ ⟧C → Set
\end{code}

%<*EqC>
\begin{code}
EQC : ∀ Γ → ⟦ Γ ⟧C → ⟦ Γ ⟧C → Set
EQC₂ : ∀ {Γ} {a₁ a₂ b₁ b₂ : ⟦ Γ ⟧C} → 
  EQC Γ a₁ a₂ → EQC Γ b₁ b₂ → EQC Γ a₁ b₁ → EQC Γ a₂ b₂ → Set
\end{code}
%</EqC>

\begin{code}
CONTEXT : Cx → TwoGraph (suc zero) zero zero
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
  isTwoGraph = record {
    Fill = λ γ* → EQC₂ (RefGraph.Square.north γ*) (RefGraph.Square.south γ*) (RefGraph.Square.west γ*) (RefGraph.Square.east γ*) }}

data Functor Γ n F where
  make-Functor : (∀ {γ γ'} (γ* : EQC Γ γ γ') → Eq (F γ) (F γ')) → Functor Γ n F
--TODO Make safe by demanding functors map reflexivity to reflexivity

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
    obj-cong₃ : ∀ {γ δ : TwoGraph.Square (CONTEXT Γ)}
      {enw : EQC Γ (TwoGraph.Square.nw {r = CONTEXT Γ} γ) (TwoGraph.Square.nw {r = CONTEXT Γ} δ)}
      {ene : EQC Γ (TwoGraph.Square.ne {r = CONTEXT Γ} γ) (TwoGraph.Square.ne {r = CONTEXT Γ} δ)}
      {esw : EQC Γ (TwoGraph.Square.sw {r = CONTEXT Γ} γ) (TwoGraph.Square.sw {r = CONTEXT Γ} δ)}
      {ese : EQC Γ (TwoGraph.Square.se {r = CONTEXT Γ} γ) (TwoGraph.Square.se {r = CONTEXT Γ} δ)}
      {γsq : TwoGraph.Fill (CONTEXT Γ) γ} {δsq : TwoGraph.Fill (CONTEXT Γ) δ}
      {sq₁ : TwoGraph.Fill (CONTEXT Γ) (record
                                         { nw = TwoGraph.Square.nw {r = CONTEXT Γ} γ
                                         ; ne = TwoGraph.Square.ne {r = CONTEXT Γ} γ
                                         ; sw = TwoGraph.Square.nw {r = CONTEXT Γ} δ
                                         ; se = TwoGraph.Square.ne {r = CONTEXT Γ} δ
                                         ; north = TwoGraph.Square.north {r = CONTEXT Γ} γ
                                         ; south = TwoGraph.Square.north {r = CONTEXT Γ} δ
                                         ; west = enw
                                         ; east = ene
                                         })}
      {sq₂ : TwoGraph.Fill (CONTEXT Γ) (record
                                         { nw = _
                                         ; ne = _
                                         ; sw = _
                                         ; se = _
                                         ; north = TwoGraph.Square.south {r = CONTEXT Γ} γ
                                         ; south = TwoGraph.Square.south {r = CONTEXT Γ} δ
                                         ; west = esw
                                         ; east = ese
                                         })}
      {sqₑ : TwoGraph.Fill (CONTEXT Γ) (record
                                         { nw = _
                                         ; ne = _
                                         ; sw = _
                                         ; se = _
                                         ; north = TwoGraph.Square.west {r = CONTEXT Γ} γ
                                         ; south = TwoGraph.Square.west {r = CONTEXT Γ} δ
                                         ; west = enw
                                         ; east = esw
                                         })}
      {sqₑ' : TwoGraph.Fill (CONTEXT Γ) (record
                                          { nw = _
                                          ; ne = _
                                          ; sw = _
                                          ; se = _
                                          ; north = TwoGraph.Square.east {r = CONTEXT Γ} γ
                                          ; south = TwoGraph.Square.east {r = CONTEXT Γ} δ
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

refT-cong : ∀ {n Γ} (S T : Typeover n Γ) (e : EqT S T) → Section (eqS (refT S) (EqTypeover-cong {n} {Γ} {S} {T} {S} {T} e e) (refT T))
refT-cong {n} {Γ} S T e = record {
  vertex = λ γ → Refn-cong (Section.vertex e γ) ;
  edge = λ γ* → Refn-cong₂ {n} (Section.edge e γ*) ;
  face = λ _ → trivial n }

--TODO Fill in
eqS-cong : ∀ {n Γ}
  {S S' T T' : Typeover n Γ}
  {S* : EqT S S'} {T* : EqT T T'} {e : EqT S T} {e' : EqT S' T'}
  {s : Section S} {s' : Section S'} {t : Section T} {t' : Section T'} →
  Section (eqS s S* s') → Section (eqS e (EqTypeover-cong {n} {_} {S} {S'} {T} {T'} S* T*) e') → Section (eqS t T* t') →
  EqT (eqS s e t) (eqS s' e' t') --TODO Reorder arguments
eqS-cong {n} s* e* t* = record { 
  vertex = λ γ → eqTTn-cong n (Section.vertex s* γ) (Section.vertex e* γ) (Section.vertex t* γ) ; 
  edge = λ γ* → eqTTn-cong₂ n (Section.edge s* γ*) (Section.edge e* γ*) (Section.edge t* γ*) ; 
  face = λ sq-fill → trivial n }

refS : ∀ {n Γ} {T : Typeover n Γ} (s : Section T) → Section (eqS s (refT T) s)
refS {n} {Γ} {T} s = record {
  vertex = λ γ → refn (Section.vertex s γ) ;
  edge = λ γ* → refn-cong {n} (Section.edge s γ*) ;
  face = λ _ → trivial n }

refS-cong : ∀ {n Γ} {S T : Typeover n Γ}
  {s : Section S} {e : EqT S T} {t : Section T}
  (p : Section (eqS s e t)) → Section (eqS {pred n} {Γ} {eqS s (refT S) s} {eqS t (refT T) t} (refS s)
     (eqS-cong {n} {Γ} {S} {T} {S} {T} {e} {e} {refT S} {refT T} {s} {t} {s} {t} p (refT-cong S T e) p) (refS t))
refS-cong {n} p = record {
  vertex = λ γ → refn-cong {!!} ;
  edge = {!!} ;
  face = {!!} }

--TODO Inline
{- TwoGraphMap : Cx → Cx → Set₁
TwoGraphMap Γ Δ = TwoGraphFunctor (CONTEXT Γ) (CONTEXT Δ)

record TwoGraphMapEq {Γ Δ} (F G : TwoGraphMap Γ Δ) : Set₁ where
  field
    vertex : ∀ γ → EQC Δ (app F γ) (app G γ)
    edge : ∀ {γ γ'} (γ* : EQC Γ γ γ') → EQC₂ (vertex γ) (vertex γ') (app₂ F γ*) (app₂ G γ*)

TypeoverF : ∀ {n} {Γ Δ} → TwoGraphMap Γ Δ → Typeover n Δ → Typeover n Γ
TypeoverF F T = record {
  obj = λ γ → Typeover.obj T (app F γ) ;
  obj-cong = make-Functor (λ γ* → ap₂ (Typeover.obj-cong T) (app₂ F γ*)) ;
  obj-cong₂ = make-Functor₂ (λ γ₁* γ₂* γₑ γₑ' sq-fill → ap₃ (Typeover.obj-cong₂ T) (app₂ F γ₁*) (app₂ F γ₂*) (app₂ F γₑ) (app₂ F γₑ') (app₃ F sq-fill)) ;
  obj-cong₃ = Typeover.obj-cong₃ T}

Typeover-eq : ∀ {n Γ Δ ⟦ρ⟧ ⟦σ⟧} (T : Typeover n Δ) →
  TwoGraphMapEq ⟦ρ⟧ ⟦σ⟧ →
  (F : Section (TypeoverF ⟦ρ⟧ T))
  (G : Section (TypeoverF ⟦σ⟧ T)) →
  Typeover (pred n) Γ
Typeover-eq {n} {⟦ρ⟧ = ⟦ρ⟧} {⟦σ⟧} T ⟦τ⟧ F G = record {
  obj = λ γ → eqTTn (Section.vertex F γ) (ap₂ (Typeover.obj-cong T) (TwoGraphMapEq.vertex ⟦τ⟧ γ)) (Section.vertex G γ) ;
  obj-cong = make-Functor (λ {γ} {γ'} γ* → eqTTn-cong n (Section.edge F γ*) (ap₃ (Typeover.obj-cong₂ T) (TwoGraphMapEq.vertex ⟦τ⟧ _) (TwoGraphMapEq.vertex ⟦τ⟧ _) (app₂ ⟦ρ⟧ γ*) (app₂ ⟦σ⟧ γ*) (TwoGraphMapEq.edge ⟦τ⟧ γ*)) (Section.edge G γ*)) ;
  obj-cong₂ = make-Functor₂ (λ γ₁* γ₂* γₑ γₑ' sq-fill → eqTTn-cong₂ n (Section.face F sq-fill) (Typeover.obj-cong₃ T) (Section.face G sq-fill)) ;
  obj-cong₃ = trivial n } -}
\end{code}
