/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2091 : Family 7 := level7.get ⟨37,by decide⟩
def sourceMap2091 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 5) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 7 0 4 v)
def fusedMap2091 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 0 4 v)
theorem sourceMap2091_checked : acceptsGraphIso
    (source (graph core2091) (root 7) 0 4) DegreeTwoThreeSpectrum1788.graph sourceMap2091=true := by decide +kernel
theorem fusedMap2091_checked : acceptsGraphIso
    (fused (graph core2091) (root 7) 0 4) DegreeTwoThreeSpectrum1790.graph fusedMap2091=true := by decide +kernel
theorem certified2091 : Certified (graph core2091) (root 7) 0 4 :=
  of_native_maps core2091 DegreeTwoThreeSpectrum1788.graph DegreeTwoThreeSpectrum1790.graph
    sourceMap2091 fusedMap2091 sourceMap2091_checked fusedMap2091_checked
    DegreeTwoThreeFiniteComparisons.comparison2091
#print axioms sourceMap2091_checked
#print axioms fusedMap2091_checked
#print axioms certified2091
def sourceMap2091swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,9,10,11,12,13,8] (sourceLabel 7 4 0 v)
def fusedMap2091swap : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 4 0 v)
theorem sourceMap2091swap_checked : acceptsGraphIso
    (source (graph core2091) (root 7) 4 0) DegreeTwoThreeSpectrum1788.graph sourceMap2091swap=true := by decide +kernel
theorem fusedMap2091swap_checked : acceptsGraphIso
    (fused (graph core2091) (root 7) 4 0) DegreeTwoThreeSpectrum1790.graph fusedMap2091swap=true := by decide +kernel
theorem certified2091swap : Certified (graph core2091) (root 7) 4 0 :=
  of_native_maps core2091 DegreeTwoThreeSpectrum1788.graph DegreeTwoThreeSpectrum1790.graph
    sourceMap2091swap fusedMap2091swap sourceMap2091swap_checked fusedMap2091swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2091
#print axioms sourceMap2091swap_checked
#print axioms fusedMap2091swap_checked
#print axioms certified2091swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
