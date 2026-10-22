/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2268 : Family 9 := level9.get ⟨203,by decide⟩
def sourceMap2268 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2268 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2268_checked : acceptsGraphIso
    (source (graph core2268) (root 9) 0 4) DegreeTwoThreeSpectrum4413.graph sourceMap2268=true := by decide +kernel
theorem fusedMap2268_checked : acceptsGraphIso
    (fused (graph core2268) (root 9) 0 4) DegreeTwoThreeSpectrum3985.graph fusedMap2268=true := by decide +kernel
theorem certified2268 : Certified (graph core2268) (root 9) 0 4 :=
  of_native_maps core2268 DegreeTwoThreeSpectrum4413.graph DegreeTwoThreeSpectrum3985.graph
    sourceMap2268 fusedMap2268 sourceMap2268_checked fusedMap2268_checked
    DegreeTwoThreeFiniteComparisons.comparison2268
#print axioms sourceMap2268_checked
#print axioms fusedMap2268_checked
#print axioms certified2268
def sourceMap2268swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2268swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2268swap_checked : acceptsGraphIso
    (source (graph core2268) (root 9) 4 0) DegreeTwoThreeSpectrum4413.graph sourceMap2268swap=true := by decide +kernel
theorem fusedMap2268swap_checked : acceptsGraphIso
    (fused (graph core2268) (root 9) 4 0) DegreeTwoThreeSpectrum3985.graph fusedMap2268swap=true := by decide +kernel
theorem certified2268swap : Certified (graph core2268) (root 9) 4 0 :=
  of_native_maps core2268 DegreeTwoThreeSpectrum4413.graph DegreeTwoThreeSpectrum3985.graph
    sourceMap2268swap fusedMap2268swap sourceMap2268swap_checked fusedMap2268swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2268
#print axioms sourceMap2268swap_checked
#print axioms fusedMap2268swap_checked
#print axioms certified2268swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
