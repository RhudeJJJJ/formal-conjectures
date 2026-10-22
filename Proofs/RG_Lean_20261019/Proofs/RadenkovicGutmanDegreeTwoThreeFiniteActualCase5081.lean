/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5081 : Family 6 := level6.get ⟨41,by decide⟩
def sourceMap5081 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,5,6,7,8,9,10,2,3,4,0,11,12,13,14] (sourceLabel 6 2 4 v)
def fusedMap5081 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14] (fusedLabel 6 2 4 v)
theorem sourceMap5081_checked : acceptsGraphIso
    (source (graph core5081) (root 6) 2 4) DegreeTwoThreeSpectrum3649.graph sourceMap5081=true := by decide +kernel
theorem fusedMap5081_checked : acceptsGraphIso
    (fused (graph core5081) (root 6) 2 4) DegreeTwoThreeSpectrum2505.graph fusedMap5081=true := by decide +kernel
theorem certified5081 : Certified (graph core5081) (root 6) 2 4 :=
  of_native_maps core5081 DegreeTwoThreeSpectrum3649.graph DegreeTwoThreeSpectrum2505.graph
    sourceMap5081 fusedMap5081 sourceMap5081_checked fusedMap5081_checked
    DegreeTwoThreeFiniteComparisons.comparison5081
#print axioms sourceMap5081_checked
#print axioms fusedMap5081_checked
#print axioms certified5081
def sourceMap5081swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,5,6,7,8,9,10,0,11,12,13,14,2,3,4] (sourceLabel 6 4 2 v)
def fusedMap5081swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14] (fusedLabel 6 4 2 v)
theorem sourceMap5081swap_checked : acceptsGraphIso
    (source (graph core5081) (root 6) 4 2) DegreeTwoThreeSpectrum3649.graph sourceMap5081swap=true := by decide +kernel
theorem fusedMap5081swap_checked : acceptsGraphIso
    (fused (graph core5081) (root 6) 4 2) DegreeTwoThreeSpectrum2505.graph fusedMap5081swap=true := by decide +kernel
theorem certified5081swap : Certified (graph core5081) (root 6) 4 2 :=
  of_native_maps core5081 DegreeTwoThreeSpectrum3649.graph DegreeTwoThreeSpectrum2505.graph
    sourceMap5081swap fusedMap5081swap sourceMap5081swap_checked fusedMap5081swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5081
#print axioms sourceMap5081swap_checked
#print axioms fusedMap5081swap_checked
#print axioms certified5081swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
