/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1584 : Family 10 := level10.get ⟨553,by decide⟩
def sourceMap1584 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,14,11,12,13,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1584 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1584_checked : acceptsGraphIso
    (source (graph core1584) (root 10) 0 2) DegreeTwoThreeSpectrum3149.graph sourceMap1584=true := by decide +kernel
theorem fusedMap1584_checked : acceptsGraphIso
    (fused (graph core1584) (root 10) 0 2) DegreeTwoThreeSpectrum2492.graph fusedMap1584=true := by decide +kernel
theorem certified1584 : Certified (graph core1584) (root 10) 0 2 :=
  of_native_maps core1584 DegreeTwoThreeSpectrum3149.graph DegreeTwoThreeSpectrum2492.graph
    sourceMap1584 fusedMap1584 sourceMap1584_checked fusedMap1584_checked
    DegreeTwoThreeFiniteComparisons.comparison1584
#print axioms sourceMap1584_checked
#print axioms fusedMap1584_checked
#print axioms certified1584
def sourceMap1584swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,14,11,12,8,9,10,13] (sourceLabel 10 2 0 v)
def fusedMap1584swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1584swap_checked : acceptsGraphIso
    (source (graph core1584) (root 10) 2 0) DegreeTwoThreeSpectrum3149.graph sourceMap1584swap=true := by decide +kernel
theorem fusedMap1584swap_checked : acceptsGraphIso
    (fused (graph core1584) (root 10) 2 0) DegreeTwoThreeSpectrum2492.graph fusedMap1584swap=true := by decide +kernel
theorem certified1584swap : Certified (graph core1584) (root 10) 2 0 :=
  of_native_maps core1584 DegreeTwoThreeSpectrum3149.graph DegreeTwoThreeSpectrum2492.graph
    sourceMap1584swap fusedMap1584swap sourceMap1584swap_checked fusedMap1584swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1584
#print axioms sourceMap1584swap_checked
#print axioms fusedMap1584swap_checked
#print axioms certified1584swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
