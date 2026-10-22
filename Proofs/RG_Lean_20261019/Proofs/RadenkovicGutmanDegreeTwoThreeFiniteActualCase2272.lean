/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2272 : Family 9 := level9.get ⟨216,by decide⟩
def sourceMap2272 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2272 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2272_checked : acceptsGraphIso
    (source (graph core2272) (root 9) 0 4) DegreeTwoThreeSpectrum4455.graph sourceMap2272=true := by decide +kernel
theorem fusedMap2272_checked : acceptsGraphIso
    (fused (graph core2272) (root 9) 0 4) DegreeTwoThreeSpectrum4003.graph fusedMap2272=true := by decide +kernel
theorem certified2272 : Certified (graph core2272) (root 9) 0 4 :=
  of_native_maps core2272 DegreeTwoThreeSpectrum4455.graph DegreeTwoThreeSpectrum4003.graph
    sourceMap2272 fusedMap2272 sourceMap2272_checked fusedMap2272_checked
    DegreeTwoThreeFiniteComparisons.comparison2272
#print axioms sourceMap2272_checked
#print axioms fusedMap2272_checked
#print axioms certified2272
def sourceMap2272swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2272swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2272swap_checked : acceptsGraphIso
    (source (graph core2272) (root 9) 4 0) DegreeTwoThreeSpectrum4455.graph sourceMap2272swap=true := by decide +kernel
theorem fusedMap2272swap_checked : acceptsGraphIso
    (fused (graph core2272) (root 9) 4 0) DegreeTwoThreeSpectrum4003.graph fusedMap2272swap=true := by decide +kernel
theorem certified2272swap : Certified (graph core2272) (root 9) 4 0 :=
  of_native_maps core2272 DegreeTwoThreeSpectrum4455.graph DegreeTwoThreeSpectrum4003.graph
    sourceMap2272swap fusedMap2272swap sourceMap2272swap_checked fusedMap2272swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2272
#print axioms sourceMap2272swap_checked
#print axioms fusedMap2272swap_checked
#print axioms certified2272swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
