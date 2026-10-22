/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1828 : Family 10 := level10.get ⟨1201,by decide⟩
def sourceMap1828 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,14,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1828 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1828_checked : acceptsGraphIso
    (source (graph core1828) (root 10) 0 2) DegreeTwoThreeSpectrum3320.graph sourceMap1828=true := by decide +kernel
theorem fusedMap1828_checked : acceptsGraphIso
    (fused (graph core1828) (root 10) 0 2) DegreeTwoThreeSpectrum3324.graph fusedMap1828=true := by decide +kernel
theorem certified1828 : Certified (graph core1828) (root 10) 0 2 :=
  of_native_maps core1828 DegreeTwoThreeSpectrum3320.graph DegreeTwoThreeSpectrum3324.graph
    sourceMap1828 fusedMap1828 sourceMap1828_checked fusedMap1828_checked
    DegreeTwoThreeFiniteComparisons.comparison1828
#print axioms sourceMap1828_checked
#print axioms fusedMap1828_checked
#print axioms certified1828
def sourceMap1828swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,8,9,10,14] (sourceLabel 10 2 0 v)
def fusedMap1828swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1828swap_checked : acceptsGraphIso
    (source (graph core1828) (root 10) 2 0) DegreeTwoThreeSpectrum3320.graph sourceMap1828swap=true := by decide +kernel
theorem fusedMap1828swap_checked : acceptsGraphIso
    (fused (graph core1828) (root 10) 2 0) DegreeTwoThreeSpectrum3324.graph fusedMap1828swap=true := by decide +kernel
theorem certified1828swap : Certified (graph core1828) (root 10) 2 0 :=
  of_native_maps core1828 DegreeTwoThreeSpectrum3320.graph DegreeTwoThreeSpectrum3324.graph
    sourceMap1828swap fusedMap1828swap sourceMap1828swap_checked fusedMap1828swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1828
#print axioms sourceMap1828swap_checked
#print axioms fusedMap1828swap_checked
#print axioms certified1828swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
