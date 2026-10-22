/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1765 : Family 10 := level10.get ⟨1047,by decide⟩
def sourceMap1765 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1765 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1765_checked : acceptsGraphIso
    (source (graph core1765) (root 10) 0 2) DegreeTwoThreeSpectrum3084.graph sourceMap1765=true := by decide +kernel
theorem fusedMap1765_checked : acceptsGraphIso
    (fused (graph core1765) (root 10) 0 2) DegreeTwoThreeSpectrum3085.graph fusedMap1765=true := by decide +kernel
theorem certified1765 : Certified (graph core1765) (root 10) 0 2 :=
  of_native_maps core1765 DegreeTwoThreeSpectrum3084.graph DegreeTwoThreeSpectrum3085.graph
    sourceMap1765 fusedMap1765 sourceMap1765_checked fusedMap1765_checked
    DegreeTwoThreeFiniteComparisons.comparison1765
#print axioms sourceMap1765_checked
#print axioms fusedMap1765_checked
#print axioms certified1765
def sourceMap1765swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1765swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1765swap_checked : acceptsGraphIso
    (source (graph core1765) (root 10) 2 0) DegreeTwoThreeSpectrum3084.graph sourceMap1765swap=true := by decide +kernel
theorem fusedMap1765swap_checked : acceptsGraphIso
    (fused (graph core1765) (root 10) 2 0) DegreeTwoThreeSpectrum3085.graph fusedMap1765swap=true := by decide +kernel
theorem certified1765swap : Certified (graph core1765) (root 10) 2 0 :=
  of_native_maps core1765 DegreeTwoThreeSpectrum3084.graph DegreeTwoThreeSpectrum3085.graph
    sourceMap1765swap fusedMap1765swap sourceMap1765swap_checked fusedMap1765swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1765
#print axioms sourceMap1765swap_checked
#print axioms fusedMap1765swap_checked
#print axioms certified1765swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
