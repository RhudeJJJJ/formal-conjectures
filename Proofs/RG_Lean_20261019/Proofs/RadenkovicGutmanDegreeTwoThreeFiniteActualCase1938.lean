/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1938 : Family 10 := level10.get ⟨1460,by decide⟩
def sourceMap1938 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,7,8,9,10,11,12,13,14,4,5,6,1,2,3] (sourceLabel 10 0 2 v)
def fusedMap1938 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1938_checked : acceptsGraphIso
    (source (graph core1938) (root 10) 0 2) DegreeTwoThreeSpectrum3678.graph sourceMap1938=true := by decide +kernel
theorem fusedMap1938_checked : acceptsGraphIso
    (fused (graph core1938) (root 10) 0 2) DegreeTwoThreeSpectrum3697.graph fusedMap1938=true := by decide +kernel
theorem certified1938 : Certified (graph core1938) (root 10) 0 2 :=
  of_native_maps core1938 DegreeTwoThreeSpectrum3678.graph DegreeTwoThreeSpectrum3697.graph
    sourceMap1938 fusedMap1938 sourceMap1938_checked fusedMap1938_checked
    DegreeTwoThreeFiniteComparisons.comparison1938
#print axioms sourceMap1938_checked
#print axioms fusedMap1938_checked
#print axioms certified1938
def sourceMap1938swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,7,8,9,10,11,12,13,14,4,5,1,2,3,6] (sourceLabel 10 2 0 v)
def fusedMap1938swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1938swap_checked : acceptsGraphIso
    (source (graph core1938) (root 10) 2 0) DegreeTwoThreeSpectrum3678.graph sourceMap1938swap=true := by decide +kernel
theorem fusedMap1938swap_checked : acceptsGraphIso
    (fused (graph core1938) (root 10) 2 0) DegreeTwoThreeSpectrum3697.graph fusedMap1938swap=true := by decide +kernel
theorem certified1938swap : Certified (graph core1938) (root 10) 2 0 :=
  of_native_maps core1938 DegreeTwoThreeSpectrum3678.graph DegreeTwoThreeSpectrum3697.graph
    sourceMap1938swap fusedMap1938swap sourceMap1938swap_checked fusedMap1938swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1938
#print axioms sourceMap1938swap_checked
#print axioms fusedMap1938swap_checked
#print axioms certified1938swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
