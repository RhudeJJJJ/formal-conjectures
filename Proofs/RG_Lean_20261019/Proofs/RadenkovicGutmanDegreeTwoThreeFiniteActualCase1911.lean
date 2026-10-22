/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1911 : Family 10 := level10.get ⟨1393,by decide⟩
def sourceMap1911 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,1,2,3,4,5,9,6,7,8] (sourceLabel 10 0 2 v)
def fusedMap1911 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,14,6,7,8,9] (fusedLabel 10 0 2 v)
theorem sourceMap1911_checked : acceptsGraphIso
    (source (graph core1911) (root 10) 0 2) DegreeTwoThreeSpectrum3420.graph sourceMap1911=true := by decide +kernel
theorem fusedMap1911_checked : acceptsGraphIso
    (fused (graph core1911) (root 10) 0 2) DegreeTwoThreeSpectrum3607.graph fusedMap1911=true := by decide +kernel
theorem certified1911 : Certified (graph core1911) (root 10) 0 2 :=
  of_native_maps core1911 DegreeTwoThreeSpectrum3420.graph DegreeTwoThreeSpectrum3607.graph
    sourceMap1911 fusedMap1911 sourceMap1911_checked fusedMap1911_checked
    DegreeTwoThreeFiniteComparisons.comparison1911
#print axioms sourceMap1911_checked
#print axioms fusedMap1911_checked
#print axioms certified1911
def sourceMap1911swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,1,2,3,4,5,6,7,8,9] (sourceLabel 10 2 0 v)
def fusedMap1911swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,14,6,7,8,9] (fusedLabel 10 2 0 v)
theorem sourceMap1911swap_checked : acceptsGraphIso
    (source (graph core1911) (root 10) 2 0) DegreeTwoThreeSpectrum3420.graph sourceMap1911swap=true := by decide +kernel
theorem fusedMap1911swap_checked : acceptsGraphIso
    (fused (graph core1911) (root 10) 2 0) DegreeTwoThreeSpectrum3607.graph fusedMap1911swap=true := by decide +kernel
theorem certified1911swap : Certified (graph core1911) (root 10) 2 0 :=
  of_native_maps core1911 DegreeTwoThreeSpectrum3420.graph DegreeTwoThreeSpectrum3607.graph
    sourceMap1911swap fusedMap1911swap sourceMap1911swap_checked fusedMap1911swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1911
#print axioms sourceMap1911swap_checked
#print axioms fusedMap1911swap_checked
#print axioms certified1911swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
