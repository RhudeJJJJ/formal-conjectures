/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2451 : Family 9 := level9.get ⟨691,by decide⟩
def sourceMap2451 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2451 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2451_checked : acceptsGraphIso
    (source (graph core2451) (root 9) 0 4) DegreeTwoThreeSpectrum4666.graph sourceMap2451=true := by decide +kernel
theorem fusedMap2451_checked : acceptsGraphIso
    (fused (graph core2451) (root 9) 0 4) DegreeTwoThreeSpectrum4667.graph fusedMap2451=true := by decide +kernel
theorem certified2451 : Certified (graph core2451) (root 9) 0 4 :=
  of_native_maps core2451 DegreeTwoThreeSpectrum4666.graph DegreeTwoThreeSpectrum4667.graph
    sourceMap2451 fusedMap2451 sourceMap2451_checked fusedMap2451_checked
    DegreeTwoThreeFiniteComparisons.comparison2451
#print axioms sourceMap2451_checked
#print axioms fusedMap2451_checked
#print axioms certified2451
def sourceMap2451swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2451swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2451swap_checked : acceptsGraphIso
    (source (graph core2451) (root 9) 4 0) DegreeTwoThreeSpectrum4666.graph sourceMap2451swap=true := by decide +kernel
theorem fusedMap2451swap_checked : acceptsGraphIso
    (fused (graph core2451) (root 9) 4 0) DegreeTwoThreeSpectrum4667.graph fusedMap2451swap=true := by decide +kernel
theorem certified2451swap : Certified (graph core2451) (root 9) 4 0 :=
  of_native_maps core2451 DegreeTwoThreeSpectrum4666.graph DegreeTwoThreeSpectrum4667.graph
    sourceMap2451swap fusedMap2451swap sourceMap2451swap_checked fusedMap2451swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2451
#print axioms sourceMap2451swap_checked
#print axioms fusedMap2451swap_checked
#print axioms certified2451swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
