/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1873 : Family 10 := level10.get ⟨1311,by decide⟩
def sourceMap1873 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1873 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1873_checked : acceptsGraphIso
    (source (graph core1873) (root 10) 0 2) DegreeTwoThreeSpectrum3479.graph sourceMap1873=true := by decide +kernel
theorem fusedMap1873_checked : acceptsGraphIso
    (fused (graph core1873) (root 10) 0 2) DegreeTwoThreeSpectrum3481.graph fusedMap1873=true := by decide +kernel
theorem certified1873 : Certified (graph core1873) (root 10) 0 2 :=
  of_native_maps core1873 DegreeTwoThreeSpectrum3479.graph DegreeTwoThreeSpectrum3481.graph
    sourceMap1873 fusedMap1873 sourceMap1873_checked fusedMap1873_checked
    DegreeTwoThreeFiniteComparisons.comparison1873
#print axioms sourceMap1873_checked
#print axioms fusedMap1873_checked
#print axioms certified1873
def sourceMap1873swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1873swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1873swap_checked : acceptsGraphIso
    (source (graph core1873) (root 10) 2 0) DegreeTwoThreeSpectrum3479.graph sourceMap1873swap=true := by decide +kernel
theorem fusedMap1873swap_checked : acceptsGraphIso
    (fused (graph core1873) (root 10) 2 0) DegreeTwoThreeSpectrum3481.graph fusedMap1873swap=true := by decide +kernel
theorem certified1873swap : Certified (graph core1873) (root 10) 2 0 :=
  of_native_maps core1873 DegreeTwoThreeSpectrum3479.graph DegreeTwoThreeSpectrum3481.graph
    sourceMap1873swap fusedMap1873swap sourceMap1873swap_checked fusedMap1873swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1873
#print axioms sourceMap1873swap_checked
#print axioms fusedMap1873swap_checked
#print axioms certified1873swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
