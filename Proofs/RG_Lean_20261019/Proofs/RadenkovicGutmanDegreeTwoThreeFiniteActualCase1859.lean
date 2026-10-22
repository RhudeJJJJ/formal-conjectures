/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1859 : Family 10 := level10.get ⟨1278,by decide⟩
def sourceMap1859 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1859 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1859_checked : acceptsGraphIso
    (source (graph core1859) (root 10) 0 2) DegreeTwoThreeSpectrum3432.graph sourceMap1859=true := by decide +kernel
theorem fusedMap1859_checked : acceptsGraphIso
    (fused (graph core1859) (root 10) 0 2) DegreeTwoThreeSpectrum3434.graph fusedMap1859=true := by decide +kernel
theorem certified1859 : Certified (graph core1859) (root 10) 0 2 :=
  of_native_maps core1859 DegreeTwoThreeSpectrum3432.graph DegreeTwoThreeSpectrum3434.graph
    sourceMap1859 fusedMap1859 sourceMap1859_checked fusedMap1859_checked
    DegreeTwoThreeFiniteComparisons.comparison1859
#print axioms sourceMap1859_checked
#print axioms fusedMap1859_checked
#print axioms certified1859
def sourceMap1859swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1859swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1859swap_checked : acceptsGraphIso
    (source (graph core1859) (root 10) 2 0) DegreeTwoThreeSpectrum3432.graph sourceMap1859swap=true := by decide +kernel
theorem fusedMap1859swap_checked : acceptsGraphIso
    (fused (graph core1859) (root 10) 2 0) DegreeTwoThreeSpectrum3434.graph fusedMap1859swap=true := by decide +kernel
theorem certified1859swap : Certified (graph core1859) (root 10) 2 0 :=
  of_native_maps core1859 DegreeTwoThreeSpectrum3432.graph DegreeTwoThreeSpectrum3434.graph
    sourceMap1859swap fusedMap1859swap sourceMap1859swap_checked fusedMap1859swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1859
#print axioms sourceMap1859swap_checked
#print axioms fusedMap1859swap_checked
#print axioms certified1859swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
