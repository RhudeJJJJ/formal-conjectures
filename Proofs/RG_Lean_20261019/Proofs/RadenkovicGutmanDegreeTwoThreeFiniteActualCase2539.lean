/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2539 : Family 10 := level10.get ⟨349,by decide⟩
def sourceMap2539 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2539 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2539_checked : acceptsGraphIso
    (source (graph core2539) (root 10) 0 4) DegreeTwoThreeSpectrum5617.graph sourceMap2539=true := by decide +kernel
theorem fusedMap2539_checked : acceptsGraphIso
    (fused (graph core2539) (root 10) 0 4) DegreeTwoThreeSpectrum5618.graph fusedMap2539=true := by decide +kernel
theorem certified2539 : Certified (graph core2539) (root 10) 0 4 :=
  of_native_maps core2539 DegreeTwoThreeSpectrum5617.graph DegreeTwoThreeSpectrum5618.graph
    sourceMap2539 fusedMap2539 sourceMap2539_checked fusedMap2539_checked
    DegreeTwoThreeFiniteComparisons.comparison2539
#print axioms sourceMap2539_checked
#print axioms fusedMap2539_checked
#print axioms certified2539
def sourceMap2539swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2539swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2539swap_checked : acceptsGraphIso
    (source (graph core2539) (root 10) 4 0) DegreeTwoThreeSpectrum5617.graph sourceMap2539swap=true := by decide +kernel
theorem fusedMap2539swap_checked : acceptsGraphIso
    (fused (graph core2539) (root 10) 4 0) DegreeTwoThreeSpectrum5618.graph fusedMap2539swap=true := by decide +kernel
theorem certified2539swap : Certified (graph core2539) (root 10) 4 0 :=
  of_native_maps core2539 DegreeTwoThreeSpectrum5617.graph DegreeTwoThreeSpectrum5618.graph
    sourceMap2539swap fusedMap2539swap sourceMap2539swap_checked fusedMap2539swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2539
#print axioms sourceMap2539swap_checked
#print axioms fusedMap2539swap_checked
#print axioms certified2539swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
