/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1438 : Family 10 := level10.get ⟨50,by decide⟩
def sourceMap1438 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![2,1,0,9,10,11,12,13,14,8,6,7,3,4,5] (sourceLabel 10 0 2 v)
def fusedMap1438 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![2,1,0,9,10,11,12,13,14,8,7,3,4,5,6] (fusedLabel 10 0 2 v)
theorem sourceMap1438_checked : acceptsGraphIso
    (source (graph core1438) (root 10) 0 2) DegreeTwoThreeSpectrum2388.graph sourceMap1438=true := by decide +kernel
theorem fusedMap1438_checked : acceptsGraphIso
    (fused (graph core1438) (root 10) 0 2) DegreeTwoThreeSpectrum2422.graph fusedMap1438=true := by decide +kernel
theorem certified1438 : Certified (graph core1438) (root 10) 0 2 :=
  of_native_maps core1438 DegreeTwoThreeSpectrum2388.graph DegreeTwoThreeSpectrum2422.graph
    sourceMap1438 fusedMap1438 sourceMap1438_checked fusedMap1438_checked
    DegreeTwoThreeFiniteComparisons.comparison1438
#print axioms sourceMap1438_checked
#print axioms fusedMap1438_checked
#print axioms certified1438
def sourceMap1438swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![2,1,0,9,10,11,12,13,14,8,6,3,4,5,7] (sourceLabel 10 2 0 v)
def fusedMap1438swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![2,1,0,9,10,11,12,13,14,8,7,3,4,5,6] (fusedLabel 10 2 0 v)
theorem sourceMap1438swap_checked : acceptsGraphIso
    (source (graph core1438) (root 10) 2 0) DegreeTwoThreeSpectrum2388.graph sourceMap1438swap=true := by decide +kernel
theorem fusedMap1438swap_checked : acceptsGraphIso
    (fused (graph core1438) (root 10) 2 0) DegreeTwoThreeSpectrum2422.graph fusedMap1438swap=true := by decide +kernel
theorem certified1438swap : Certified (graph core1438) (root 10) 2 0 :=
  of_native_maps core1438 DegreeTwoThreeSpectrum2388.graph DegreeTwoThreeSpectrum2422.graph
    sourceMap1438swap fusedMap1438swap sourceMap1438swap_checked fusedMap1438swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1438
#print axioms sourceMap1438swap_checked
#print axioms fusedMap1438swap_checked
#print axioms certified1438swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
