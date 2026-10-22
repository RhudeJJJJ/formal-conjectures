/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1957 : Family 10 := level10.get ⟨1512,by decide⟩
def sourceMap1957 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,11,12,13,14,4,5,6,7,8,9,10,1,2,3] (sourceLabel 10 0 2 v)
def fusedMap1957 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,9,10,11,12,13,14,5,6,7,8] (fusedLabel 10 0 2 v)
theorem sourceMap1957_checked : acceptsGraphIso
    (source (graph core1957) (root 10) 0 2) DegreeTwoThreeSpectrum3636.graph sourceMap1957=true := by decide +kernel
theorem fusedMap1957_checked : acceptsGraphIso
    (fused (graph core1957) (root 10) 0 2) DegreeTwoThreeSpectrum3730.graph fusedMap1957=true := by decide +kernel
theorem certified1957 : Certified (graph core1957) (root 10) 0 2 :=
  of_native_maps core1957 DegreeTwoThreeSpectrum3636.graph DegreeTwoThreeSpectrum3730.graph
    sourceMap1957 fusedMap1957 sourceMap1957_checked fusedMap1957_checked
    DegreeTwoThreeFiniteComparisons.comparison1957
#print axioms sourceMap1957_checked
#print axioms fusedMap1957_checked
#print axioms certified1957
def sourceMap1957swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,11,12,13,14,4,5,6,7,8,9,1,2,3,10] (sourceLabel 10 2 0 v)
def fusedMap1957swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,9,10,11,12,13,14,5,6,7,8] (fusedLabel 10 2 0 v)
theorem sourceMap1957swap_checked : acceptsGraphIso
    (source (graph core1957) (root 10) 2 0) DegreeTwoThreeSpectrum3636.graph sourceMap1957swap=true := by decide +kernel
theorem fusedMap1957swap_checked : acceptsGraphIso
    (fused (graph core1957) (root 10) 2 0) DegreeTwoThreeSpectrum3730.graph fusedMap1957swap=true := by decide +kernel
theorem certified1957swap : Certified (graph core1957) (root 10) 2 0 :=
  of_native_maps core1957 DegreeTwoThreeSpectrum3636.graph DegreeTwoThreeSpectrum3730.graph
    sourceMap1957swap fusedMap1957swap sourceMap1957swap_checked fusedMap1957swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1957
#print axioms sourceMap1957swap_checked
#print axioms fusedMap1957swap_checked
#print axioms certified1957swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
