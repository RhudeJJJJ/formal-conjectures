/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1861 : Family 10 := level10.get ⟨1282,by decide⟩
def sourceMap1861 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1861 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1861_checked : acceptsGraphIso
    (source (graph core1861) (root 10) 0 2) DegreeTwoThreeSpectrum3437.graph sourceMap1861=true := by decide +kernel
theorem fusedMap1861_checked : acceptsGraphIso
    (fused (graph core1861) (root 10) 0 2) DegreeTwoThreeSpectrum3439.graph fusedMap1861=true := by decide +kernel
theorem certified1861 : Certified (graph core1861) (root 10) 0 2 :=
  of_native_maps core1861 DegreeTwoThreeSpectrum3437.graph DegreeTwoThreeSpectrum3439.graph
    sourceMap1861 fusedMap1861 sourceMap1861_checked fusedMap1861_checked
    DegreeTwoThreeFiniteComparisons.comparison1861
#print axioms sourceMap1861_checked
#print axioms fusedMap1861_checked
#print axioms certified1861
def sourceMap1861swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1861swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1861swap_checked : acceptsGraphIso
    (source (graph core1861) (root 10) 2 0) DegreeTwoThreeSpectrum3437.graph sourceMap1861swap=true := by decide +kernel
theorem fusedMap1861swap_checked : acceptsGraphIso
    (fused (graph core1861) (root 10) 2 0) DegreeTwoThreeSpectrum3439.graph fusedMap1861swap=true := by decide +kernel
theorem certified1861swap : Certified (graph core1861) (root 10) 2 0 :=
  of_native_maps core1861 DegreeTwoThreeSpectrum3437.graph DegreeTwoThreeSpectrum3439.graph
    sourceMap1861swap fusedMap1861swap sourceMap1861swap_checked fusedMap1861swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1861
#print axioms sourceMap1861swap_checked
#print axioms fusedMap1861swap_checked
#print axioms certified1861swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
