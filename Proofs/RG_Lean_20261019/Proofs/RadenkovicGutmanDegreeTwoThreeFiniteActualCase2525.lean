/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2525 : Family 10 := level10.get ⟨298,by decide⟩
def sourceMap2525 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2525 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2525_checked : acceptsGraphIso
    (source (graph core2525) (root 10) 0 4) DegreeTwoThreeSpectrum5469.graph sourceMap2525=true := by decide +kernel
theorem fusedMap2525_checked : acceptsGraphIso
    (fused (graph core2525) (root 10) 0 4) DegreeTwoThreeSpectrum5470.graph fusedMap2525=true := by decide +kernel
theorem certified2525 : Certified (graph core2525) (root 10) 0 4 :=
  of_native_maps core2525 DegreeTwoThreeSpectrum5469.graph DegreeTwoThreeSpectrum5470.graph
    sourceMap2525 fusedMap2525 sourceMap2525_checked fusedMap2525_checked
    DegreeTwoThreeFiniteComparisons.comparison2525
#print axioms sourceMap2525_checked
#print axioms fusedMap2525_checked
#print axioms certified2525
def sourceMap2525swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2525swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2525swap_checked : acceptsGraphIso
    (source (graph core2525) (root 10) 4 0) DegreeTwoThreeSpectrum5469.graph sourceMap2525swap=true := by decide +kernel
theorem fusedMap2525swap_checked : acceptsGraphIso
    (fused (graph core2525) (root 10) 4 0) DegreeTwoThreeSpectrum5470.graph fusedMap2525swap=true := by decide +kernel
theorem certified2525swap : Certified (graph core2525) (root 10) 4 0 :=
  of_native_maps core2525 DegreeTwoThreeSpectrum5469.graph DegreeTwoThreeSpectrum5470.graph
    sourceMap2525swap fusedMap2525swap sourceMap2525swap_checked fusedMap2525swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2525
#print axioms sourceMap2525swap_checked
#print axioms fusedMap2525swap_checked
#print axioms certified2525swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
