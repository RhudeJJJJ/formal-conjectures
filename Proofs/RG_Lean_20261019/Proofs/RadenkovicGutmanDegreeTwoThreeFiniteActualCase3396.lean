/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3396 : Family 9 := level9.get ⟨481,by decide⟩
def sourceMap3396 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3396 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3396_checked : acceptsGraphIso
    (source (graph core3396) (root 9) 0 5) DegreeTwoThreeSpectrum6768.graph sourceMap3396=true := by decide +kernel
theorem fusedMap3396_checked : acceptsGraphIso
    (fused (graph core3396) (root 9) 0 5) DegreeTwoThreeSpectrum5602.graph fusedMap3396=true := by decide +kernel
theorem certified3396 : Certified (graph core3396) (root 9) 0 5 :=
  of_native_maps core3396 DegreeTwoThreeSpectrum6768.graph DegreeTwoThreeSpectrum5602.graph
    sourceMap3396 fusedMap3396 sourceMap3396_checked fusedMap3396_checked
    DegreeTwoThreeFiniteComparisons.comparison3396
#print axioms sourceMap3396_checked
#print axioms fusedMap3396_checked
#print axioms certified3396
def sourceMap3396swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3396swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3396swap_checked : acceptsGraphIso
    (source (graph core3396) (root 9) 5 0) DegreeTwoThreeSpectrum6768.graph sourceMap3396swap=true := by decide +kernel
theorem fusedMap3396swap_checked : acceptsGraphIso
    (fused (graph core3396) (root 9) 5 0) DegreeTwoThreeSpectrum5602.graph fusedMap3396swap=true := by decide +kernel
theorem certified3396swap : Certified (graph core3396) (root 9) 5 0 :=
  of_native_maps core3396 DegreeTwoThreeSpectrum6768.graph DegreeTwoThreeSpectrum5602.graph
    sourceMap3396swap fusedMap3396swap sourceMap3396swap_checked fusedMap3396swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3396
#print axioms sourceMap3396swap_checked
#print axioms fusedMap3396swap_checked
#print axioms certified3396swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
