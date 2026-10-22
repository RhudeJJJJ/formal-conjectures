/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2348 : Family 9 := level9.get ⟨420,by decide⟩
def sourceMap2348 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2348 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2348_checked : acceptsGraphIso
    (source (graph core2348) (root 9) 0 4) DegreeTwoThreeSpectrum4401.graph sourceMap2348=true := by decide +kernel
theorem fusedMap2348_checked : acceptsGraphIso
    (fused (graph core2348) (root 9) 0 4) DegreeTwoThreeSpectrum4402.graph fusedMap2348=true := by decide +kernel
theorem certified2348 : Certified (graph core2348) (root 9) 0 4 :=
  of_native_maps core2348 DegreeTwoThreeSpectrum4401.graph DegreeTwoThreeSpectrum4402.graph
    sourceMap2348 fusedMap2348 sourceMap2348_checked fusedMap2348_checked
    DegreeTwoThreeFiniteComparisons.comparison2348
#print axioms sourceMap2348_checked
#print axioms fusedMap2348_checked
#print axioms certified2348
def sourceMap2348swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2348swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2348swap_checked : acceptsGraphIso
    (source (graph core2348) (root 9) 4 0) DegreeTwoThreeSpectrum4401.graph sourceMap2348swap=true := by decide +kernel
theorem fusedMap2348swap_checked : acceptsGraphIso
    (fused (graph core2348) (root 9) 4 0) DegreeTwoThreeSpectrum4402.graph fusedMap2348swap=true := by decide +kernel
theorem certified2348swap : Certified (graph core2348) (root 9) 4 0 :=
  of_native_maps core2348 DegreeTwoThreeSpectrum4401.graph DegreeTwoThreeSpectrum4402.graph
    sourceMap2348swap fusedMap2348swap sourceMap2348swap_checked fusedMap2348swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2348
#print axioms sourceMap2348swap_checked
#print axioms fusedMap2348swap_checked
#print axioms certified2348swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
