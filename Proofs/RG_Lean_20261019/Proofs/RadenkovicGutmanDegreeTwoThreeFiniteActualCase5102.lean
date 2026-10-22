/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5102 : Family 7 := level7.get ⟨67,by decide⟩
def sourceMap5102 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,11,8,9,10,0,12,13,14,15] (sourceLabel 7 2 4 v)
def fusedMap5102 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 2 4 v)
theorem sourceMap5102_checked : acceptsGraphIso
    (source (graph core5102) (root 7) 2 4) DegreeTwoThreeSpectrum4702.graph sourceMap5102=true := by decide +kernel
theorem fusedMap5102_checked : acceptsGraphIso
    (fused (graph core5102) (root 7) 2 4) DegreeTwoThreeSpectrum3899.graph fusedMap5102=true := by decide +kernel
theorem certified5102 : Certified (graph core5102) (root 7) 2 4 :=
  of_native_maps core5102 DegreeTwoThreeSpectrum4702.graph DegreeTwoThreeSpectrum3899.graph
    sourceMap5102 fusedMap5102 sourceMap5102_checked fusedMap5102_checked
    DegreeTwoThreeFiniteComparisons.comparison5102
#print axioms sourceMap5102_checked
#print axioms fusedMap5102_checked
#print axioms certified5102
def sourceMap5102swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,11,0,12,13,14,15,8,9,10] (sourceLabel 7 4 2 v)
def fusedMap5102swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 4 2 v)
theorem sourceMap5102swap_checked : acceptsGraphIso
    (source (graph core5102) (root 7) 4 2) DegreeTwoThreeSpectrum4702.graph sourceMap5102swap=true := by decide +kernel
theorem fusedMap5102swap_checked : acceptsGraphIso
    (fused (graph core5102) (root 7) 4 2) DegreeTwoThreeSpectrum3899.graph fusedMap5102swap=true := by decide +kernel
theorem certified5102swap : Certified (graph core5102) (root 7) 4 2 :=
  of_native_maps core5102 DegreeTwoThreeSpectrum4702.graph DegreeTwoThreeSpectrum3899.graph
    sourceMap5102swap fusedMap5102swap sourceMap5102swap_checked fusedMap5102swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5102
#print axioms sourceMap5102swap_checked
#print axioms fusedMap5102swap_checked
#print axioms certified5102swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
