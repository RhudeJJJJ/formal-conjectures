/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1951 : Family 10 := level10.get ⟨1494,by decide⟩
def sourceMap1951 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,11,12,13,14,1,2,3,4,5,6,10,7,8,9] (sourceLabel 10 0 2 v)
def fusedMap1951 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,9,10,11,12,13,14,5,6,7,8] (fusedLabel 10 0 2 v)
theorem sourceMap1951_checked : acceptsGraphIso
    (source (graph core1951) (root 10) 0 2) DegreeTwoThreeSpectrum3043.graph sourceMap1951=true := by decide +kernel
theorem fusedMap1951_checked : acceptsGraphIso
    (fused (graph core1951) (root 10) 0 2) DegreeTwoThreeSpectrum3723.graph fusedMap1951=true := by decide +kernel
theorem certified1951 : Certified (graph core1951) (root 10) 0 2 :=
  of_native_maps core1951 DegreeTwoThreeSpectrum3043.graph DegreeTwoThreeSpectrum3723.graph
    sourceMap1951 fusedMap1951 sourceMap1951_checked fusedMap1951_checked
    DegreeTwoThreeFiniteComparisons.comparison1951
#print axioms sourceMap1951_checked
#print axioms fusedMap1951_checked
#print axioms certified1951
def sourceMap1951swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,11,12,13,14,1,2,3,4,5,6,7,8,9,10] (sourceLabel 10 2 0 v)
def fusedMap1951swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,9,10,11,12,13,14,5,6,7,8] (fusedLabel 10 2 0 v)
theorem sourceMap1951swap_checked : acceptsGraphIso
    (source (graph core1951) (root 10) 2 0) DegreeTwoThreeSpectrum3043.graph sourceMap1951swap=true := by decide +kernel
theorem fusedMap1951swap_checked : acceptsGraphIso
    (fused (graph core1951) (root 10) 2 0) DegreeTwoThreeSpectrum3723.graph fusedMap1951swap=true := by decide +kernel
theorem certified1951swap : Certified (graph core1951) (root 10) 2 0 :=
  of_native_maps core1951 DegreeTwoThreeSpectrum3043.graph DegreeTwoThreeSpectrum3723.graph
    sourceMap1951swap fusedMap1951swap sourceMap1951swap_checked fusedMap1951swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1951
#print axioms sourceMap1951swap_checked
#print axioms fusedMap1951swap_checked
#print axioms certified1951swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
