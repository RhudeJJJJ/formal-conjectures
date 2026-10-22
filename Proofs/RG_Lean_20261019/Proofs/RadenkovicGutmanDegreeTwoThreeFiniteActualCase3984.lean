/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3984 : Family 7 := level7.get ⟨101,by decide⟩
def sourceMap3984 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 6) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,11,9,10,1,0,12,13,14,15] (sourceLabel 7 1 5 v)
def fusedMap3984 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15] (fusedLabel 7 1 5 v)
theorem sourceMap3984_checked : acceptsGraphIso
    (source (graph core3984) (root 7) 1 5) DegreeTwoThreeSpectrum4673.graph sourceMap3984=true := by decide +kernel
theorem fusedMap3984_checked : acceptsGraphIso
    (fused (graph core3984) (root 7) 1 5) DegreeTwoThreeSpectrum4176.graph fusedMap3984=true := by decide +kernel
theorem certified3984 : Certified (graph core3984) (root 7) 1 5 :=
  of_native_maps core3984 DegreeTwoThreeSpectrum4673.graph DegreeTwoThreeSpectrum4176.graph
    sourceMap3984 fusedMap3984 sourceMap3984_checked fusedMap3984_checked
    DegreeTwoThreeFiniteComparisons.comparison3984
#print axioms sourceMap3984_checked
#print axioms fusedMap3984_checked
#print axioms certified3984
def sourceMap3984swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 2) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,11,1,0,12,13,14,15,9,10] (sourceLabel 7 5 1 v)
def fusedMap3984swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15] (fusedLabel 7 5 1 v)
theorem sourceMap3984swap_checked : acceptsGraphIso
    (source (graph core3984) (root 7) 5 1) DegreeTwoThreeSpectrum4673.graph sourceMap3984swap=true := by decide +kernel
theorem fusedMap3984swap_checked : acceptsGraphIso
    (fused (graph core3984) (root 7) 5 1) DegreeTwoThreeSpectrum4176.graph fusedMap3984swap=true := by decide +kernel
theorem certified3984swap : Certified (graph core3984) (root 7) 5 1 :=
  of_native_maps core3984 DegreeTwoThreeSpectrum4673.graph DegreeTwoThreeSpectrum4176.graph
    sourceMap3984swap fusedMap3984swap sourceMap3984swap_checked fusedMap3984swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3984
#print axioms sourceMap3984swap_checked
#print axioms fusedMap3984swap_checked
#print axioms certified3984swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
