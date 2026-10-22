/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1985 : Family 10 := level10.get ⟨1585,by decide⟩
def sourceMap1985 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1985 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1985_checked : acceptsGraphIso
    (source (graph core1985) (root 10) 0 2) DegreeTwoThreeSpectrum3769.graph sourceMap1985=true := by decide +kernel
theorem fusedMap1985_checked : acceptsGraphIso
    (fused (graph core1985) (root 10) 0 2) DegreeTwoThreeSpectrum3083.graph fusedMap1985=true := by decide +kernel
theorem certified1985 : Certified (graph core1985) (root 10) 0 2 :=
  of_native_maps core1985 DegreeTwoThreeSpectrum3769.graph DegreeTwoThreeSpectrum3083.graph
    sourceMap1985 fusedMap1985 sourceMap1985_checked fusedMap1985_checked
    DegreeTwoThreeFiniteComparisons.comparison1985
#print axioms sourceMap1985_checked
#print axioms fusedMap1985_checked
#print axioms certified1985
def sourceMap1985swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1985swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1985swap_checked : acceptsGraphIso
    (source (graph core1985) (root 10) 2 0) DegreeTwoThreeSpectrum3769.graph sourceMap1985swap=true := by decide +kernel
theorem fusedMap1985swap_checked : acceptsGraphIso
    (fused (graph core1985) (root 10) 2 0) DegreeTwoThreeSpectrum3083.graph fusedMap1985swap=true := by decide +kernel
theorem certified1985swap : Certified (graph core1985) (root 10) 2 0 :=
  of_native_maps core1985 DegreeTwoThreeSpectrum3769.graph DegreeTwoThreeSpectrum3083.graph
    sourceMap1985swap fusedMap1985swap sourceMap1985swap_checked fusedMap1985swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1985
#print axioms sourceMap1985swap_checked
#print axioms fusedMap1985swap_checked
#print axioms certified1985swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
