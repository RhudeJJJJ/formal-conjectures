/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1807 : Family 10 := level10.get ⟨1155,by decide⟩
def sourceMap1807 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1807 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1807_checked : acceptsGraphIso
    (source (graph core1807) (root 10) 0 2) DegreeTwoThreeSpectrum3249.graph sourceMap1807=true := by decide +kernel
theorem fusedMap1807_checked : acceptsGraphIso
    (fused (graph core1807) (root 10) 0 2) DegreeTwoThreeSpectrum3250.graph fusedMap1807=true := by decide +kernel
theorem certified1807 : Certified (graph core1807) (root 10) 0 2 :=
  of_native_maps core1807 DegreeTwoThreeSpectrum3249.graph DegreeTwoThreeSpectrum3250.graph
    sourceMap1807 fusedMap1807 sourceMap1807_checked fusedMap1807_checked
    DegreeTwoThreeFiniteComparisons.comparison1807
#print axioms sourceMap1807_checked
#print axioms fusedMap1807_checked
#print axioms certified1807
def sourceMap1807swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1807swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1807swap_checked : acceptsGraphIso
    (source (graph core1807) (root 10) 2 0) DegreeTwoThreeSpectrum3249.graph sourceMap1807swap=true := by decide +kernel
theorem fusedMap1807swap_checked : acceptsGraphIso
    (fused (graph core1807) (root 10) 2 0) DegreeTwoThreeSpectrum3250.graph fusedMap1807swap=true := by decide +kernel
theorem certified1807swap : Certified (graph core1807) (root 10) 2 0 :=
  of_native_maps core1807 DegreeTwoThreeSpectrum3249.graph DegreeTwoThreeSpectrum3250.graph
    sourceMap1807swap fusedMap1807swap sourceMap1807swap_checked fusedMap1807swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1807
#print axioms sourceMap1807swap_checked
#print axioms fusedMap1807swap_checked
#print axioms certified1807swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
