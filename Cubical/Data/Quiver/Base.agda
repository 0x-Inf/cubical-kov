-- A Quiver is an endo-span of types.
--   ob <- mor -> ob
-- This is often used in set theory as the data over which a category
-- is defined to be algebraic structure.

-- A Quiver is equivalent to a Graph (modulo universe issues), but
-- they are not definitionally isomorphic: turning a quiver into a
-- graph introduces a Path between objects/nodes in the definition of
-- an Edge.

-- Since avoiding Paths generally leads to cleaner code, Graphs or
-- Quivers may be preferable depending on the variance of a
-- construction.

-- 1. *Using* a Graph generally requires fewer paths between
--    objects. For instance, Graphs are preferable to be used in the
--    definition of a category because composition can be defined by
--    sharing a common middle variable Hom[ A , B ] × Hom[ B , C ] →
--    Hom[ A , C ], which in a Quiver would need a path (e e' : mor) →
--    (cod e ≡ dom e') → mor.
--
-- 2. *Producing* a Quiver generally requires fewer paths between
--    objects. For instance, Quivers are preferable to be used in the
--    definition of generating data for free and presented categories.
--    As an example, the "Funny tensor product" C ⊗ D of categories is
--    defined by generators and relations. The generators are easy to
--    define as a Quiver, but if defined as a graph, then the
--    generators require a path between objects.

-- So as a principle, to get the most general definitions,
-- 1. *Produce* Graphs
-- 2. *Use* Quivers
-- when you can get away with it.

module Cubical.Data.Quiver.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Graph.Base
open import Cubical.Data.Graph.Displayed as DG hiding (Section)
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.UnderlyingGraph
open import Cubical.Categories.Displayed.Base

private
  variable
   ℓC ℓC' ℓg ℓg' ℓgᴰ ℓgᴰ' ℓq ℓq' ℓh ℓh' ℓj ℓ : Level

-- Useful in certain applications to separate this into components
record QuiverOver (ob : Type ℓg) ℓg' : Type (ℓ-suc (ℓ-max ℓg ℓg')) where
  field
    mor : Type ℓg'
    dom : mor → ob
    cod : mor → ob

open QuiverOver
Quiver : ∀ ℓg ℓg' → Type _
Quiver ℓg ℓg' = Σ[ ob ∈ Type ℓg ] QuiverOver ob ℓg'

-- A "heteromorphism" from a Quiver to a Graph
record HetQG (Q : Quiver ℓq ℓq') (G : Graph ℓg ℓg')
       : Type (ℓ-max (ℓ-max ℓq ℓq') (ℓ-max ℓg ℓg')) where
  field
    _$g_ : Q .fst → G .Node
    _<$g>_ : (e : Q .snd .mor)
           → G .Edge (_$g_ (Q .snd .dom e)) (_$g_ (Q .snd .cod e))
open HetQG public

module _ {G : Graph ℓg ℓg'}
         {H : Graph ℓh ℓh'}
         {Q : Quiver ℓq ℓq'}
         where
  compGrHomHetQG : GraphHom G H → HetQG Q G → HetQG Q H
  compGrHomHetQG ϕ h ._$g_   q = ϕ GraphHom.$g (h HetQG.$g q)
  compGrHomHetQG ϕ h ._<$g>_ e = ϕ GraphHom.<$g> (h HetQG.<$g> e)

-- Universal property:
-- HetQG Q G ≅ QHom Q (Graph→Quiver G)
Graph→Quiver : Graph ℓg ℓg' → Quiver ℓg (ℓ-max ℓg ℓg')
Graph→Quiver g .fst = g .Node
Graph→Quiver g .snd .mor = Σ[ A ∈ g .Node ] Σ[ B ∈ g .Node ] g .Edge A B
Graph→Quiver g .snd .dom x = x .fst
Graph→Quiver g .snd .cod x = x .snd .fst

-- | The use of ≡ in this definition is the raison d'etre for the
-- | Quiver-Graph distinction
-- HetQG Q G ≅ QHom (Quiver→Graph Q) G
Quiver→Graph : Quiver ℓq ℓq' → Graph ℓq (ℓ-max ℓq ℓq')
Quiver→Graph Q .Node = Q .fst
Quiver→Graph Q .Edge A B =
  Σ[ e ∈ Q .snd .mor ]
    (Q .snd .dom e ≡ A)
  × (Q .snd .cod e ≡ B)

Cat→Quiver : Category ℓC ℓC' → Quiver _ _
Cat→Quiver 𝓒 = Graph→Quiver (Cat→Graph 𝓒)

-- A "heterogeneous" local section of a displayed graph
module _ {Q : Quiver ℓq ℓq'}{G : Graph ℓg ℓg'}
         (ϕ : HetQG Q G)
         (Gᴰ : Graphᴰ G ℓgᴰ ℓgᴰ')
         where
  private
    module Gᴰ = Graphᴰ Gᴰ
  open HetQG
  record HetSection : Type (ℓ-max (ℓ-max ℓq ℓq')
                        (ℓ-max (ℓ-max ℓg ℓg')
                        (ℓ-max ℓgᴰ ℓgᴰ'))) where
    field
      _$gᴰ_ : ∀ (u : Q .fst) → Gᴰ.Node[ ϕ $g u ]
      _<$g>ᴰ_ : ∀ (e : Q .snd .mor)
              → Gᴰ.Edge[ ϕ <$g> e
                ][ _$gᴰ_ (Q .snd .dom e)
                 , _$gᴰ_ (Q .snd .cod e) ]
