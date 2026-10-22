/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2438 : Family 9 := level9.get ⟨638,by decide⟩
def sourceMap2438 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2438 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2438_checked : acceptsGraphIso
    (source (graph core2438) (root 9) 0 4) DegreeTwoThreeSpectrum4795.graph sourceMap2438=true := by decide +kernel
theorem fusedMap2438_checked : acceptsGraphIso
    (fused (graph core2438) (root 9) 0 4) DegreeTwoThreeSpectrum4403.graph fusedMap2438=true := by decide +kernel
theorem certified2438 : Certified (graph core2438) (root 9) 0 4 :=
  of_native_maps core2438 DegreeTwoThreeSpectrum4795.graph DegreeTwoThreeSpectrum4403.graph
    sourceMap2438 fusedMap2438 sourceMap2438_checked fusedMap2438_checked
    DegreeTwoThreeFiniteComparisons.comparison2438
#print axioms sourceMap2438_checked
#print axioms fusedMap2438_checked
#print axioms certified2438
def sourceMap2438swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2438swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2438swap_checked : acceptsGraphIso
    (source (graph core2438) (root 9) 4 0) DegreeTwoThreeSpectrum4795.graph sourceMap2438swap=true := by decide +kernel
theorem fusedMap2438swap_checked : acceptsGraphIso
    (fused (graph core2438) (root 9) 4 0) DegreeTwoThreeSpectrum4403.graph fusedMap2438swap=true := by decide +kernel
theorem certified2438swap : Certified (graph core2438) (root 9) 4 0 :=
  of_native_maps core2438 DegreeTwoThreeSpectrum4795.graph DegreeTwoThreeSpectrum4403.graph
    sourceMap2438swap fusedMap2438swap sourceMap2438swap_checked fusedMap2438swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2438
#print axioms sourceMap2438swap_checked
#print axioms fusedMap2438swap_checked
#print axioms certified2438swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
