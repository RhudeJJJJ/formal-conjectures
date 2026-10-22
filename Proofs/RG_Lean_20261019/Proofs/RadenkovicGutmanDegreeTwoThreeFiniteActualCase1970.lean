/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1970 : Family 10 := level10.get ⟨1552,by decide⟩
def sourceMap1970 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1970 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1970_checked : acceptsGraphIso
    (source (graph core1970) (root 10) 0 2) DegreeTwoThreeSpectrum3753.graph sourceMap1970=true := by decide +kernel
theorem fusedMap1970_checked : acceptsGraphIso
    (fused (graph core1970) (root 10) 0 2) DegreeTwoThreeSpectrum3030.graph fusedMap1970=true := by decide +kernel
theorem certified1970 : Certified (graph core1970) (root 10) 0 2 :=
  of_native_maps core1970 DegreeTwoThreeSpectrum3753.graph DegreeTwoThreeSpectrum3030.graph
    sourceMap1970 fusedMap1970 sourceMap1970_checked fusedMap1970_checked
    DegreeTwoThreeFiniteComparisons.comparison1970
#print axioms sourceMap1970_checked
#print axioms fusedMap1970_checked
#print axioms certified1970
def sourceMap1970swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1970swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1970swap_checked : acceptsGraphIso
    (source (graph core1970) (root 10) 2 0) DegreeTwoThreeSpectrum3753.graph sourceMap1970swap=true := by decide +kernel
theorem fusedMap1970swap_checked : acceptsGraphIso
    (fused (graph core1970) (root 10) 2 0) DegreeTwoThreeSpectrum3030.graph fusedMap1970swap=true := by decide +kernel
theorem certified1970swap : Certified (graph core1970) (root 10) 2 0 :=
  of_native_maps core1970 DegreeTwoThreeSpectrum3753.graph DegreeTwoThreeSpectrum3030.graph
    sourceMap1970swap fusedMap1970swap sourceMap1970swap_checked fusedMap1970swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1970
#print axioms sourceMap1970swap_checked
#print axioms fusedMap1970swap_checked
#print axioms certified1970swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
