/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3501 : Family 6 := level6.get ⟨41,by decide⟩
def sourceMap3501 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (sourceLabel 6 0 6 v)
def fusedMap3501 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14] (fusedLabel 6 0 6 v)
theorem sourceMap3501_checked : acceptsGraphIso
    (source (graph core3501) (root 6) 0 6) DegreeTwoThreeSpectrum2502.graph sourceMap3501=true := by decide +kernel
theorem fusedMap3501_checked : acceptsGraphIso
    (fused (graph core3501) (root 6) 0 6) DegreeTwoThreeSpectrum2505.graph fusedMap3501=true := by decide +kernel
theorem certified3501 : Certified (graph core3501) (root 6) 0 6 :=
  of_native_maps core3501 DegreeTwoThreeSpectrum2502.graph DegreeTwoThreeSpectrum2505.graph
    sourceMap3501 fusedMap3501 sourceMap3501_checked fusedMap3501_checked
    DegreeTwoThreeFiniteComparisons.comparison3501
#print axioms sourceMap3501_checked
#print axioms fusedMap3501_checked
#print axioms certified3501
def sourceMap3501swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 1) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,10,11,12,13,14,9] (sourceLabel 6 6 0 v)
def fusedMap3501swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14] (fusedLabel 6 6 0 v)
theorem sourceMap3501swap_checked : acceptsGraphIso
    (source (graph core3501) (root 6) 6 0) DegreeTwoThreeSpectrum2502.graph sourceMap3501swap=true := by decide +kernel
theorem fusedMap3501swap_checked : acceptsGraphIso
    (fused (graph core3501) (root 6) 6 0) DegreeTwoThreeSpectrum2505.graph fusedMap3501swap=true := by decide +kernel
theorem certified3501swap : Certified (graph core3501) (root 6) 6 0 :=
  of_native_maps core3501 DegreeTwoThreeSpectrum2502.graph DegreeTwoThreeSpectrum2505.graph
    sourceMap3501swap fusedMap3501swap sourceMap3501swap_checked fusedMap3501swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3501
#print axioms sourceMap3501swap_checked
#print axioms fusedMap3501swap_checked
#print axioms certified3501swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
