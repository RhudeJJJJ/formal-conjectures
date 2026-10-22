/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3088 : Family 6 := level6.get ⟨9,by decide⟩
def sourceMap3088 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (sourceLabel 6 0 5 v)
def fusedMap3088 : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12,13] (fusedLabel 6 0 5 v)
theorem sourceMap3088_checked : acceptsGraphIso
    (source (graph core3088) (root 6) 0 5) DegreeTwoThreeSpectrum1792.graph sourceMap3088=true := by decide +kernel
theorem fusedMap3088_checked : acceptsGraphIso
    (fused (graph core3088) (root 6) 0 5) DegreeTwoThreeSpectrum1712.graph fusedMap3088=true := by decide +kernel
theorem certified3088 : Certified (graph core3088) (root 6) 0 5 :=
  of_native_maps core3088 DegreeTwoThreeSpectrum1792.graph DegreeTwoThreeSpectrum1712.graph
    sourceMap3088 fusedMap3088 sourceMap3088_checked fusedMap3088_checked
    DegreeTwoThreeFiniteComparisons.comparison3088
#print axioms sourceMap3088_checked
#print axioms fusedMap3088_checked
#print axioms certified3088
def sourceMap3088swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,12,13,8] (sourceLabel 6 5 0 v)
def fusedMap3088swap : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12,13] (fusedLabel 6 5 0 v)
theorem sourceMap3088swap_checked : acceptsGraphIso
    (source (graph core3088) (root 6) 5 0) DegreeTwoThreeSpectrum1792.graph sourceMap3088swap=true := by decide +kernel
theorem fusedMap3088swap_checked : acceptsGraphIso
    (fused (graph core3088) (root 6) 5 0) DegreeTwoThreeSpectrum1712.graph fusedMap3088swap=true := by decide +kernel
theorem certified3088swap : Certified (graph core3088) (root 6) 5 0 :=
  of_native_maps core3088 DegreeTwoThreeSpectrum1792.graph DegreeTwoThreeSpectrum1712.graph
    sourceMap3088swap fusedMap3088swap sourceMap3088swap_checked fusedMap3088swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3088
#print axioms sourceMap3088swap_checked
#print axioms fusedMap3088swap_checked
#print axioms certified3088swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
