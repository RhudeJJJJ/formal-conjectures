/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1844 : Family 10 := level10.get ⟨1233,by decide⟩
def sourceMap1844 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![5,0,1,2,3,4,9,10,11,12,13,14,6,7,8] (sourceLabel 10 0 2 v)
def fusedMap1844 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,14,6,7,8,9] (fusedLabel 10 0 2 v)
theorem sourceMap1844_checked : acceptsGraphIso
    (source (graph core1844) (root 10) 0 2) DegreeTwoThreeSpectrum3360.graph sourceMap1844=true := by decide +kernel
theorem fusedMap1844_checked : acceptsGraphIso
    (fused (graph core1844) (root 10) 0 2) DegreeTwoThreeSpectrum3375.graph fusedMap1844=true := by decide +kernel
theorem certified1844 : Certified (graph core1844) (root 10) 0 2 :=
  of_native_maps core1844 DegreeTwoThreeSpectrum3360.graph DegreeTwoThreeSpectrum3375.graph
    sourceMap1844 fusedMap1844 sourceMap1844_checked fusedMap1844_checked
    DegreeTwoThreeFiniteComparisons.comparison1844
#print axioms sourceMap1844_checked
#print axioms fusedMap1844_checked
#print axioms certified1844
def sourceMap1844swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![5,0,1,2,3,4,9,10,11,12,13,6,7,8,14] (sourceLabel 10 2 0 v)
def fusedMap1844swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,14,6,7,8,9] (fusedLabel 10 2 0 v)
theorem sourceMap1844swap_checked : acceptsGraphIso
    (source (graph core1844) (root 10) 2 0) DegreeTwoThreeSpectrum3360.graph sourceMap1844swap=true := by decide +kernel
theorem fusedMap1844swap_checked : acceptsGraphIso
    (fused (graph core1844) (root 10) 2 0) DegreeTwoThreeSpectrum3375.graph fusedMap1844swap=true := by decide +kernel
theorem certified1844swap : Certified (graph core1844) (root 10) 2 0 :=
  of_native_maps core1844 DegreeTwoThreeSpectrum3360.graph DegreeTwoThreeSpectrum3375.graph
    sourceMap1844swap fusedMap1844swap sourceMap1844swap_checked fusedMap1844swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1844
#print axioms sourceMap1844swap_checked
#print axioms fusedMap1844swap_checked
#print axioms certified1844swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
