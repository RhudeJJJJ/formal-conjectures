/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1893 : Family 10 := level10.get ⟨1358,by decide⟩
def sourceMap1893 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1893 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1893_checked : acceptsGraphIso
    (source (graph core1893) (root 10) 0 2) DegreeTwoThreeSpectrum3549.graph sourceMap1893=true := by decide +kernel
theorem fusedMap1893_checked : acceptsGraphIso
    (fused (graph core1893) (root 10) 0 2) DegreeTwoThreeSpectrum3551.graph fusedMap1893=true := by decide +kernel
theorem certified1893 : Certified (graph core1893) (root 10) 0 2 :=
  of_native_maps core1893 DegreeTwoThreeSpectrum3549.graph DegreeTwoThreeSpectrum3551.graph
    sourceMap1893 fusedMap1893 sourceMap1893_checked fusedMap1893_checked
    DegreeTwoThreeFiniteComparisons.comparison1893
#print axioms sourceMap1893_checked
#print axioms fusedMap1893_checked
#print axioms certified1893
def sourceMap1893swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1893swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1893swap_checked : acceptsGraphIso
    (source (graph core1893) (root 10) 2 0) DegreeTwoThreeSpectrum3549.graph sourceMap1893swap=true := by decide +kernel
theorem fusedMap1893swap_checked : acceptsGraphIso
    (fused (graph core1893) (root 10) 2 0) DegreeTwoThreeSpectrum3551.graph fusedMap1893swap=true := by decide +kernel
theorem certified1893swap : Certified (graph core1893) (root 10) 2 0 :=
  of_native_maps core1893 DegreeTwoThreeSpectrum3549.graph DegreeTwoThreeSpectrum3551.graph
    sourceMap1893swap fusedMap1893swap sourceMap1893swap_checked fusedMap1893swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1893
#print axioms sourceMap1893swap_checked
#print axioms fusedMap1893swap_checked
#print axioms certified1893swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
