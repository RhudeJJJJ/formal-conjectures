/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2187 : Family 8 := level8.get ⟨203,by decide⟩
def sourceMap2187 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2187 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2187_checked : acceptsGraphIso
    (source (graph core2187) (root 8) 0 4) DegreeTwoThreeSpectrum3119.graph sourceMap2187=true := by decide +kernel
theorem fusedMap2187_checked : acceptsGraphIso
    (fused (graph core2187) (root 8) 0 4) DegreeTwoThreeSpectrum2473.graph fusedMap2187=true := by decide +kernel
theorem certified2187 : Certified (graph core2187) (root 8) 0 4 :=
  of_native_maps core2187 DegreeTwoThreeSpectrum3119.graph DegreeTwoThreeSpectrum2473.graph
    sourceMap2187 fusedMap2187 sourceMap2187_checked fusedMap2187_checked
    DegreeTwoThreeFiniteComparisons.comparison2187
#print axioms sourceMap2187_checked
#print axioms fusedMap2187_checked
#print axioms certified2187
def sourceMap2187swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,10] (sourceLabel 8 4 0 v)
def fusedMap2187swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2187swap_checked : acceptsGraphIso
    (source (graph core2187) (root 8) 4 0) DegreeTwoThreeSpectrum3119.graph sourceMap2187swap=true := by decide +kernel
theorem fusedMap2187swap_checked : acceptsGraphIso
    (fused (graph core2187) (root 8) 4 0) DegreeTwoThreeSpectrum2473.graph fusedMap2187swap=true := by decide +kernel
theorem certified2187swap : Certified (graph core2187) (root 8) 4 0 :=
  of_native_maps core2187 DegreeTwoThreeSpectrum3119.graph DegreeTwoThreeSpectrum2473.graph
    sourceMap2187swap fusedMap2187swap sourceMap2187swap_checked fusedMap2187swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2187
#print axioms sourceMap2187swap_checked
#print axioms fusedMap2187swap_checked
#print axioms certified2187swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
