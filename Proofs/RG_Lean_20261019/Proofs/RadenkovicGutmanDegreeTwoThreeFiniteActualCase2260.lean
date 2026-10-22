/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2260 : Family 9 := level9.get ⟨181,by decide⟩
def sourceMap2260 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2260 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2260_checked : acceptsGraphIso
    (source (graph core2260) (root 9) 0 4) DegreeTwoThreeSpectrum4358.graph sourceMap2260=true := by decide +kernel
theorem fusedMap2260_checked : acceptsGraphIso
    (fused (graph core2260) (root 9) 0 4) DegreeTwoThreeSpectrum3948.graph fusedMap2260=true := by decide +kernel
theorem certified2260 : Certified (graph core2260) (root 9) 0 4 :=
  of_native_maps core2260 DegreeTwoThreeSpectrum4358.graph DegreeTwoThreeSpectrum3948.graph
    sourceMap2260 fusedMap2260 sourceMap2260_checked fusedMap2260_checked
    DegreeTwoThreeFiniteComparisons.comparison2260
#print axioms sourceMap2260_checked
#print axioms fusedMap2260_checked
#print axioms certified2260
def sourceMap2260swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2260swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2260swap_checked : acceptsGraphIso
    (source (graph core2260) (root 9) 4 0) DegreeTwoThreeSpectrum4358.graph sourceMap2260swap=true := by decide +kernel
theorem fusedMap2260swap_checked : acceptsGraphIso
    (fused (graph core2260) (root 9) 4 0) DegreeTwoThreeSpectrum3948.graph fusedMap2260swap=true := by decide +kernel
theorem certified2260swap : Certified (graph core2260) (root 9) 4 0 :=
  of_native_maps core2260 DegreeTwoThreeSpectrum4358.graph DegreeTwoThreeSpectrum3948.graph
    sourceMap2260swap fusedMap2260swap sourceMap2260swap_checked fusedMap2260swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2260
#print axioms sourceMap2260swap_checked
#print axioms fusedMap2260swap_checked
#print axioms certified2260swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
