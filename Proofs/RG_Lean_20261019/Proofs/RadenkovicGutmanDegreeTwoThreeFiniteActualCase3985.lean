/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3985 : Family 7 := level7.get ⟨102,by decide⟩
def sourceMap3985 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 6) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15] (sourceLabel 7 1 5 v)
def fusedMap3985 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15] (fusedLabel 7 1 5 v)
theorem sourceMap3985_checked : acceptsGraphIso
    (source (graph core3985) (root 7) 1 5) DegreeTwoThreeSpectrum4681.graph sourceMap3985=true := by decide +kernel
theorem fusedMap3985_checked : acceptsGraphIso
    (fused (graph core3985) (root 7) 1 5) DegreeTwoThreeSpectrum4185.graph fusedMap3985=true := by decide +kernel
theorem certified3985 : Certified (graph core3985) (root 7) 1 5 :=
  of_native_maps core3985 DegreeTwoThreeSpectrum4681.graph DegreeTwoThreeSpectrum4185.graph
    sourceMap3985 fusedMap3985 sourceMap3985_checked fusedMap3985_checked
    DegreeTwoThreeFiniteComparisons.comparison3985
#print axioms sourceMap3985_checked
#print axioms fusedMap3985_checked
#print axioms certified3985
def sourceMap3985swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 2) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,12,13,14,15,10,11] (sourceLabel 7 5 1 v)
def fusedMap3985swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15] (fusedLabel 7 5 1 v)
theorem sourceMap3985swap_checked : acceptsGraphIso
    (source (graph core3985) (root 7) 5 1) DegreeTwoThreeSpectrum4681.graph sourceMap3985swap=true := by decide +kernel
theorem fusedMap3985swap_checked : acceptsGraphIso
    (fused (graph core3985) (root 7) 5 1) DegreeTwoThreeSpectrum4185.graph fusedMap3985swap=true := by decide +kernel
theorem certified3985swap : Certified (graph core3985) (root 7) 5 1 :=
  of_native_maps core3985 DegreeTwoThreeSpectrum4681.graph DegreeTwoThreeSpectrum4185.graph
    sourceMap3985swap fusedMap3985swap sourceMap3985swap_checked fusedMap3985swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3985
#print axioms sourceMap3985swap_checked
#print axioms fusedMap3985swap_checked
#print axioms certified3985swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
