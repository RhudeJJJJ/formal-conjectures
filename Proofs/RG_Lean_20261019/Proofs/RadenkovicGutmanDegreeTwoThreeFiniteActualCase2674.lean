/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2674 : Family 10 := level10.get ⟨749,by decide⟩
def sourceMap2674 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2674 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2674_checked : acceptsGraphIso
    (source (graph core2674) (root 10) 0 4) DegreeTwoThreeSpectrum6652.graph sourceMap2674=true := by decide +kernel
theorem fusedMap2674_checked : acceptsGraphIso
    (fused (graph core2674) (root 10) 0 4) DegreeTwoThreeSpectrum5512.graph fusedMap2674=true := by decide +kernel
theorem certified2674 : Certified (graph core2674) (root 10) 0 4 :=
  of_native_maps core2674 DegreeTwoThreeSpectrum6652.graph DegreeTwoThreeSpectrum5512.graph
    sourceMap2674 fusedMap2674 sourceMap2674_checked fusedMap2674_checked
    DegreeTwoThreeFiniteComparisons.comparison2674
#print axioms sourceMap2674_checked
#print axioms fusedMap2674_checked
#print axioms certified2674
def sourceMap2674swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2674swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2674swap_checked : acceptsGraphIso
    (source (graph core2674) (root 10) 4 0) DegreeTwoThreeSpectrum6652.graph sourceMap2674swap=true := by decide +kernel
theorem fusedMap2674swap_checked : acceptsGraphIso
    (fused (graph core2674) (root 10) 4 0) DegreeTwoThreeSpectrum5512.graph fusedMap2674swap=true := by decide +kernel
theorem certified2674swap : Certified (graph core2674) (root 10) 4 0 :=
  of_native_maps core2674 DegreeTwoThreeSpectrum6652.graph DegreeTwoThreeSpectrum5512.graph
    sourceMap2674swap fusedMap2674swap sourceMap2674swap_checked fusedMap2674swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2674
#print axioms sourceMap2674swap_checked
#print axioms fusedMap2674swap_checked
#print axioms certified2674swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
