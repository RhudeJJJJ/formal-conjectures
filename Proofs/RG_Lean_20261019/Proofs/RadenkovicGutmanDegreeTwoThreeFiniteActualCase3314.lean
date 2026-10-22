/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3314 : Family 9 := level9.get ⟨278,by decide⟩
def sourceMap3314 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3314 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3314_checked : acceptsGraphIso
    (source (graph core3314) (root 9) 0 5) DegreeTwoThreeSpectrum5773.graph sourceMap3314=true := by decide +kernel
theorem fusedMap3314_checked : acceptsGraphIso
    (fused (graph core3314) (root 9) 0 5) DegreeTwoThreeSpectrum5774.graph fusedMap3314=true := by decide +kernel
theorem certified3314 : Certified (graph core3314) (root 9) 0 5 :=
  of_native_maps core3314 DegreeTwoThreeSpectrum5773.graph DegreeTwoThreeSpectrum5774.graph
    sourceMap3314 fusedMap3314 sourceMap3314_checked fusedMap3314_checked
    DegreeTwoThreeFiniteComparisons.comparison3314
#print axioms sourceMap3314_checked
#print axioms fusedMap3314_checked
#print axioms certified3314
def sourceMap3314swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3314swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3314swap_checked : acceptsGraphIso
    (source (graph core3314) (root 9) 5 0) DegreeTwoThreeSpectrum5773.graph sourceMap3314swap=true := by decide +kernel
theorem fusedMap3314swap_checked : acceptsGraphIso
    (fused (graph core3314) (root 9) 5 0) DegreeTwoThreeSpectrum5774.graph fusedMap3314swap=true := by decide +kernel
theorem certified3314swap : Certified (graph core3314) (root 9) 5 0 :=
  of_native_maps core3314 DegreeTwoThreeSpectrum5773.graph DegreeTwoThreeSpectrum5774.graph
    sourceMap3314swap fusedMap3314swap sourceMap3314swap_checked fusedMap3314swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3314
#print axioms sourceMap3314swap_checked
#print axioms fusedMap3314swap_checked
#print axioms certified3314swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
