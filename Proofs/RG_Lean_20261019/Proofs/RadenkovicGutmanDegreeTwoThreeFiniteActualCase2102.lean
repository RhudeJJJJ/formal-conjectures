/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2102 : Family 7 := level7.get ⟨67,by decide⟩
def sourceMap2102 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 5) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13] (sourceLabel 7 0 4 v)
def fusedMap2102 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 0 4 v)
theorem sourceMap2102_checked : acceptsGraphIso
    (source (graph core2102) (root 7) 0 4) DegreeTwoThreeSpectrum1963.graph sourceMap2102=true := by decide +kernel
theorem fusedMap2102_checked : acceptsGraphIso
    (fused (graph core2102) (root 7) 0 4) DegreeTwoThreeSpectrum1744.graph fusedMap2102=true := by decide +kernel
theorem certified2102 : Certified (graph core2102) (root 7) 0 4 :=
  of_native_maps core2102 DegreeTwoThreeSpectrum1963.graph DegreeTwoThreeSpectrum1744.graph
    sourceMap2102 fusedMap2102 sourceMap2102_checked fusedMap2102_checked
    DegreeTwoThreeFiniteComparisons.comparison2102
#print axioms sourceMap2102_checked
#print axioms fusedMap2102_checked
#print axioms certified2102
def sourceMap2102swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,9] (sourceLabel 7 4 0 v)
def fusedMap2102swap : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 4 0 v)
theorem sourceMap2102swap_checked : acceptsGraphIso
    (source (graph core2102) (root 7) 4 0) DegreeTwoThreeSpectrum1963.graph sourceMap2102swap=true := by decide +kernel
theorem fusedMap2102swap_checked : acceptsGraphIso
    (fused (graph core2102) (root 7) 4 0) DegreeTwoThreeSpectrum1744.graph fusedMap2102swap=true := by decide +kernel
theorem certified2102swap : Certified (graph core2102) (root 7) 4 0 :=
  of_native_maps core2102 DegreeTwoThreeSpectrum1963.graph DegreeTwoThreeSpectrum1744.graph
    sourceMap2102swap fusedMap2102swap sourceMap2102swap_checked fusedMap2102swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2102
#print axioms sourceMap2102swap_checked
#print axioms fusedMap2102swap_checked
#print axioms certified2102swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
