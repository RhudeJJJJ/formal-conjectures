/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1456 : Family 10 := level10.get ⟨135,by decide⟩
def sourceMap1456 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![2,1,0,8,9,10,11,12,13,14,6,7,3,4,5] (sourceLabel 10 0 2 v)
def fusedMap1456 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1456_checked : acceptsGraphIso
    (source (graph core1456) (root 10) 0 2) DegreeTwoThreeSpectrum2899.graph sourceMap1456=true := by decide +kernel
theorem fusedMap1456_checked : acceptsGraphIso
    (fused (graph core1456) (root 10) 0 2) DegreeTwoThreeSpectrum2397.graph fusedMap1456=true := by decide +kernel
theorem certified1456 : Certified (graph core1456) (root 10) 0 2 :=
  of_native_maps core1456 DegreeTwoThreeSpectrum2899.graph DegreeTwoThreeSpectrum2397.graph
    sourceMap1456 fusedMap1456 sourceMap1456_checked fusedMap1456_checked
    DegreeTwoThreeFiniteComparisons.comparison1456
#print axioms sourceMap1456_checked
#print axioms fusedMap1456_checked
#print axioms certified1456
def sourceMap1456swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![2,1,0,8,9,10,11,12,13,14,6,3,4,5,7] (sourceLabel 10 2 0 v)
def fusedMap1456swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1456swap_checked : acceptsGraphIso
    (source (graph core1456) (root 10) 2 0) DegreeTwoThreeSpectrum2899.graph sourceMap1456swap=true := by decide +kernel
theorem fusedMap1456swap_checked : acceptsGraphIso
    (fused (graph core1456) (root 10) 2 0) DegreeTwoThreeSpectrum2397.graph fusedMap1456swap=true := by decide +kernel
theorem certified1456swap : Certified (graph core1456) (root 10) 2 0 :=
  of_native_maps core1456 DegreeTwoThreeSpectrum2899.graph DegreeTwoThreeSpectrum2397.graph
    sourceMap1456swap fusedMap1456swap sourceMap1456swap_checked fusedMap1456swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1456
#print axioms sourceMap1456swap_checked
#print axioms fusedMap1456swap_checked
#print axioms certified1456swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
