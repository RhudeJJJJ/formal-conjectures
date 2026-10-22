/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5304 : Family 6 := level6.get ⟨39,by decide⟩
def sourceMap5304 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,6,7,8,9,10,11,3,4,5,1,0,12,13,14,15,16] (sourceLabel 6 2 6 v)
def fusedMap5304 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,10,3,2,1,0,11,12,13,14,15,16] (fusedLabel 6 2 6 v)
theorem sourceMap5304_checked : acceptsGraphIso
    (source (graph core5304) (root 6) 2 6) DegreeTwoThreeSpectrum6873.graph sourceMap5304=true := by decide +kernel
theorem fusedMap5304_checked : acceptsGraphIso
    (fused (graph core5304) (root 6) 2 6) DegreeTwoThreeSpectrum5164.graph fusedMap5304=true := by decide +kernel
theorem certified5304 : Certified (graph core5304) (root 6) 2 6 :=
  of_native_maps core5304 DegreeTwoThreeSpectrum6873.graph DegreeTwoThreeSpectrum5164.graph
    sourceMap5304 fusedMap5304 sourceMap5304_checked fusedMap5304_checked
    DegreeTwoThreeFiniteComparisons.comparison5304
#print axioms sourceMap5304_checked
#print axioms fusedMap5304_checked
#print axioms certified5304
def sourceMap5304swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,6,7,8,9,10,11,1,0,12,13,14,15,16,3,4,5] (sourceLabel 6 6 2 v)
def fusedMap5304swap : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,10,3,2,1,0,11,12,13,14,15,16] (fusedLabel 6 6 2 v)
theorem sourceMap5304swap_checked : acceptsGraphIso
    (source (graph core5304) (root 6) 6 2) DegreeTwoThreeSpectrum6873.graph sourceMap5304swap=true := by decide +kernel
theorem fusedMap5304swap_checked : acceptsGraphIso
    (fused (graph core5304) (root 6) 6 2) DegreeTwoThreeSpectrum5164.graph fusedMap5304swap=true := by decide +kernel
theorem certified5304swap : Certified (graph core5304) (root 6) 6 2 :=
  of_native_maps core5304 DegreeTwoThreeSpectrum6873.graph DegreeTwoThreeSpectrum5164.graph
    sourceMap5304swap fusedMap5304swap sourceMap5304swap_checked fusedMap5304swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5304
#print axioms sourceMap5304swap_checked
#print axioms fusedMap5304swap_checked
#print axioms certified5304swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
