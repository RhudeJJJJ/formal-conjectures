/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1984 : Family 10 := level10.get ⟨1584,by decide⟩
def sourceMap1984 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1984 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1984_checked : acceptsGraphIso
    (source (graph core1984) (root 10) 0 2) DegreeTwoThreeSpectrum3768.graph sourceMap1984=true := by decide +kernel
theorem fusedMap1984_checked : acceptsGraphIso
    (fused (graph core1984) (root 10) 0 2) DegreeTwoThreeSpectrum3082.graph fusedMap1984=true := by decide +kernel
theorem certified1984 : Certified (graph core1984) (root 10) 0 2 :=
  of_native_maps core1984 DegreeTwoThreeSpectrum3768.graph DegreeTwoThreeSpectrum3082.graph
    sourceMap1984 fusedMap1984 sourceMap1984_checked fusedMap1984_checked
    DegreeTwoThreeFiniteComparisons.comparison1984
#print axioms sourceMap1984_checked
#print axioms fusedMap1984_checked
#print axioms certified1984
def sourceMap1984swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1984swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1984swap_checked : acceptsGraphIso
    (source (graph core1984) (root 10) 2 0) DegreeTwoThreeSpectrum3768.graph sourceMap1984swap=true := by decide +kernel
theorem fusedMap1984swap_checked : acceptsGraphIso
    (fused (graph core1984) (root 10) 2 0) DegreeTwoThreeSpectrum3082.graph fusedMap1984swap=true := by decide +kernel
theorem certified1984swap : Certified (graph core1984) (root 10) 2 0 :=
  of_native_maps core1984 DegreeTwoThreeSpectrum3768.graph DegreeTwoThreeSpectrum3082.graph
    sourceMap1984swap fusedMap1984swap sourceMap1984swap_checked fusedMap1984swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1984
#print axioms sourceMap1984swap_checked
#print axioms fusedMap1984swap_checked
#print axioms certified1984swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
