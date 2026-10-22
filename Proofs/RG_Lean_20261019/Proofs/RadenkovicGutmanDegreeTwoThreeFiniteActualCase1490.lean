/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1490 : Family 10 := level10.get ⟨257,by decide⟩
def sourceMap1490 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1490 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1490_checked : acceptsGraphIso
    (source (graph core1490) (root 10) 0 2) DegreeTwoThreeSpectrum2594.graph sourceMap1490=true := by decide +kernel
theorem fusedMap1490_checked : acceptsGraphIso
    (fused (graph core1490) (root 10) 0 2) DegreeTwoThreeSpectrum2599.graph fusedMap1490=true := by decide +kernel
theorem certified1490 : Certified (graph core1490) (root 10) 0 2 :=
  of_native_maps core1490 DegreeTwoThreeSpectrum2594.graph DegreeTwoThreeSpectrum2599.graph
    sourceMap1490 fusedMap1490 sourceMap1490_checked fusedMap1490_checked
    DegreeTwoThreeFiniteComparisons.comparison1490
#print axioms sourceMap1490_checked
#print axioms fusedMap1490_checked
#print axioms certified1490
def sourceMap1490swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1490swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1490swap_checked : acceptsGraphIso
    (source (graph core1490) (root 10) 2 0) DegreeTwoThreeSpectrum2594.graph sourceMap1490swap=true := by decide +kernel
theorem fusedMap1490swap_checked : acceptsGraphIso
    (fused (graph core1490) (root 10) 2 0) DegreeTwoThreeSpectrum2599.graph fusedMap1490swap=true := by decide +kernel
theorem certified1490swap : Certified (graph core1490) (root 10) 2 0 :=
  of_native_maps core1490 DegreeTwoThreeSpectrum2594.graph DegreeTwoThreeSpectrum2599.graph
    sourceMap1490swap fusedMap1490swap sourceMap1490swap_checked fusedMap1490swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1490
#print axioms sourceMap1490swap_checked
#print axioms fusedMap1490swap_checked
#print axioms certified1490swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
