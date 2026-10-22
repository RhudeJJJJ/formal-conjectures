/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2106 : Family 7 := level7.get ⟨75,by decide⟩
def sourceMap2106 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 5) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13] (sourceLabel 7 0 4 v)
def fusedMap2106 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 0 4 v)
theorem sourceMap2106_checked : acceptsGraphIso
    (source (graph core2106) (root 7) 0 4) DegreeTwoThreeSpectrum2023.graph sourceMap2106=true := by decide +kernel
theorem fusedMap2106_checked : acceptsGraphIso
    (fused (graph core2106) (root 7) 0 4) DegreeTwoThreeSpectrum1765.graph fusedMap2106=true := by decide +kernel
theorem certified2106 : Certified (graph core2106) (root 7) 0 4 :=
  of_native_maps core2106 DegreeTwoThreeSpectrum2023.graph DegreeTwoThreeSpectrum1765.graph
    sourceMap2106 fusedMap2106 sourceMap2106_checked fusedMap2106_checked
    DegreeTwoThreeFiniteComparisons.comparison2106
#print axioms sourceMap2106_checked
#print axioms fusedMap2106_checked
#print axioms certified2106
def sourceMap2106swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,9] (sourceLabel 7 4 0 v)
def fusedMap2106swap : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 4 0 v)
theorem sourceMap2106swap_checked : acceptsGraphIso
    (source (graph core2106) (root 7) 4 0) DegreeTwoThreeSpectrum2023.graph sourceMap2106swap=true := by decide +kernel
theorem fusedMap2106swap_checked : acceptsGraphIso
    (fused (graph core2106) (root 7) 4 0) DegreeTwoThreeSpectrum1765.graph fusedMap2106swap=true := by decide +kernel
theorem certified2106swap : Certified (graph core2106) (root 7) 4 0 :=
  of_native_maps core2106 DegreeTwoThreeSpectrum2023.graph DegreeTwoThreeSpectrum1765.graph
    sourceMap2106swap fusedMap2106swap sourceMap2106swap_checked fusedMap2106swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2106
#print axioms sourceMap2106swap_checked
#print axioms fusedMap2106swap_checked
#print axioms certified2106swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
