/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1443 : Family 10 := level10.get ⟨77,by decide⟩
def sourceMap1443 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1443 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1443_checked : acceptsGraphIso
    (source (graph core1443) (root 10) 0 2) DegreeTwoThreeSpectrum2621.graph sourceMap1443=true := by decide +kernel
theorem fusedMap1443_checked : acceptsGraphIso
    (fused (graph core1443) (root 10) 0 2) DegreeTwoThreeSpectrum2337.graph fusedMap1443=true := by decide +kernel
theorem certified1443 : Certified (graph core1443) (root 10) 0 2 :=
  of_native_maps core1443 DegreeTwoThreeSpectrum2621.graph DegreeTwoThreeSpectrum2337.graph
    sourceMap1443 fusedMap1443 sourceMap1443_checked fusedMap1443_checked
    DegreeTwoThreeFiniteComparisons.comparison1443
#print axioms sourceMap1443_checked
#print axioms fusedMap1443_checked
#print axioms certified1443
def sourceMap1443swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1443swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1443swap_checked : acceptsGraphIso
    (source (graph core1443) (root 10) 2 0) DegreeTwoThreeSpectrum2621.graph sourceMap1443swap=true := by decide +kernel
theorem fusedMap1443swap_checked : acceptsGraphIso
    (fused (graph core1443) (root 10) 2 0) DegreeTwoThreeSpectrum2337.graph fusedMap1443swap=true := by decide +kernel
theorem certified1443swap : Certified (graph core1443) (root 10) 2 0 :=
  of_native_maps core1443 DegreeTwoThreeSpectrum2621.graph DegreeTwoThreeSpectrum2337.graph
    sourceMap1443swap fusedMap1443swap sourceMap1443swap_checked fusedMap1443swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1443
#print axioms sourceMap1443swap_checked
#print axioms fusedMap1443swap_checked
#print axioms certified1443swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
