/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1767 : Family 10 := level10.get ⟨1051,by decide⟩
def sourceMap1767 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1767 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1767_checked : acceptsGraphIso
    (source (graph core1767) (root 10) 0 2) DegreeTwoThreeSpectrum3091.graph sourceMap1767=true := by decide +kernel
theorem fusedMap1767_checked : acceptsGraphIso
    (fused (graph core1767) (root 10) 0 2) DegreeTwoThreeSpectrum3093.graph fusedMap1767=true := by decide +kernel
theorem certified1767 : Certified (graph core1767) (root 10) 0 2 :=
  of_native_maps core1767 DegreeTwoThreeSpectrum3091.graph DegreeTwoThreeSpectrum3093.graph
    sourceMap1767 fusedMap1767 sourceMap1767_checked fusedMap1767_checked
    DegreeTwoThreeFiniteComparisons.comparison1767
#print axioms sourceMap1767_checked
#print axioms fusedMap1767_checked
#print axioms certified1767
def sourceMap1767swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1767swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1767swap_checked : acceptsGraphIso
    (source (graph core1767) (root 10) 2 0) DegreeTwoThreeSpectrum3091.graph sourceMap1767swap=true := by decide +kernel
theorem fusedMap1767swap_checked : acceptsGraphIso
    (fused (graph core1767) (root 10) 2 0) DegreeTwoThreeSpectrum3093.graph fusedMap1767swap=true := by decide +kernel
theorem certified1767swap : Certified (graph core1767) (root 10) 2 0 :=
  of_native_maps core1767 DegreeTwoThreeSpectrum3091.graph DegreeTwoThreeSpectrum3093.graph
    sourceMap1767swap fusedMap1767swap sourceMap1767swap_checked fusedMap1767swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1767
#print axioms sourceMap1767swap_checked
#print axioms fusedMap1767swap_checked
#print axioms certified1767swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
