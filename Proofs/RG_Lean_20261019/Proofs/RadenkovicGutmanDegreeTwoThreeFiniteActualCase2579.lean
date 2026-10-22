/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2579 : Family 10 := level10.get ⟨471,by decide⟩
def sourceMap2579 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2579 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2579_checked : acceptsGraphIso
    (source (graph core2579) (root 10) 0 4) DegreeTwoThreeSpectrum5926.graph sourceMap2579=true := by decide +kernel
theorem fusedMap2579_checked : acceptsGraphIso
    (fused (graph core2579) (root 10) 0 4) DegreeTwoThreeSpectrum5927.graph fusedMap2579=true := by decide +kernel
theorem certified2579 : Certified (graph core2579) (root 10) 0 4 :=
  of_native_maps core2579 DegreeTwoThreeSpectrum5926.graph DegreeTwoThreeSpectrum5927.graph
    sourceMap2579 fusedMap2579 sourceMap2579_checked fusedMap2579_checked
    DegreeTwoThreeFiniteComparisons.comparison2579
#print axioms sourceMap2579_checked
#print axioms fusedMap2579_checked
#print axioms certified2579
def sourceMap2579swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2579swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2579swap_checked : acceptsGraphIso
    (source (graph core2579) (root 10) 4 0) DegreeTwoThreeSpectrum5926.graph sourceMap2579swap=true := by decide +kernel
theorem fusedMap2579swap_checked : acceptsGraphIso
    (fused (graph core2579) (root 10) 4 0) DegreeTwoThreeSpectrum5927.graph fusedMap2579swap=true := by decide +kernel
theorem certified2579swap : Certified (graph core2579) (root 10) 4 0 :=
  of_native_maps core2579 DegreeTwoThreeSpectrum5926.graph DegreeTwoThreeSpectrum5927.graph
    sourceMap2579swap fusedMap2579swap sourceMap2579swap_checked fusedMap2579swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2579
#print axioms sourceMap2579swap_checked
#print axioms fusedMap2579swap_checked
#print axioms certified2579swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
