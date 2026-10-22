/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1446 : Family 10 := level10.get ⟨85,by decide⟩
def sourceMap1446 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1446 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1446_checked : acceptsGraphIso
    (source (graph core1446) (root 10) 0 2) DegreeTwoThreeSpectrum2630.graph sourceMap1446=true := by decide +kernel
theorem fusedMap1446_checked : acceptsGraphIso
    (fused (graph core1446) (root 10) 0 2) DegreeTwoThreeSpectrum2344.graph fusedMap1446=true := by decide +kernel
theorem certified1446 : Certified (graph core1446) (root 10) 0 2 :=
  of_native_maps core1446 DegreeTwoThreeSpectrum2630.graph DegreeTwoThreeSpectrum2344.graph
    sourceMap1446 fusedMap1446 sourceMap1446_checked fusedMap1446_checked
    DegreeTwoThreeFiniteComparisons.comparison1446
#print axioms sourceMap1446_checked
#print axioms fusedMap1446_checked
#print axioms certified1446
def sourceMap1446swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1446swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1446swap_checked : acceptsGraphIso
    (source (graph core1446) (root 10) 2 0) DegreeTwoThreeSpectrum2630.graph sourceMap1446swap=true := by decide +kernel
theorem fusedMap1446swap_checked : acceptsGraphIso
    (fused (graph core1446) (root 10) 2 0) DegreeTwoThreeSpectrum2344.graph fusedMap1446swap=true := by decide +kernel
theorem certified1446swap : Certified (graph core1446) (root 10) 2 0 :=
  of_native_maps core1446 DegreeTwoThreeSpectrum2630.graph DegreeTwoThreeSpectrum2344.graph
    sourceMap1446swap fusedMap1446swap sourceMap1446swap_checked fusedMap1446swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1446
#print axioms sourceMap1446swap_checked
#print axioms fusedMap1446swap_checked
#print axioms certified1446swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
