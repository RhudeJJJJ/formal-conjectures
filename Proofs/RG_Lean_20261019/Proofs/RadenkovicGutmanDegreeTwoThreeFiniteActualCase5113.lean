/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5113 : Family 7 := level7.get ⟨90,by decide⟩
def sourceMap5113 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 7 2 4 v)
def fusedMap5113 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 2 4 v)
theorem sourceMap5113_checked : acceptsGraphIso
    (source (graph core5113) (root 7) 2 4) DegreeTwoThreeSpectrum4839.graph sourceMap5113=true := by decide +kernel
theorem fusedMap5113_checked : acceptsGraphIso
    (fused (graph core5113) (root 7) 2 4) DegreeTwoThreeSpectrum4018.graph fusedMap5113=true := by decide +kernel
theorem certified5113 : Certified (graph core5113) (root 7) 2 4 :=
  of_native_maps core5113 DegreeTwoThreeSpectrum4839.graph DegreeTwoThreeSpectrum4018.graph
    sourceMap5113 fusedMap5113 sourceMap5113_checked fusedMap5113_checked
    DegreeTwoThreeFiniteComparisons.comparison5113
#print axioms sourceMap5113_checked
#print axioms fusedMap5113_checked
#print axioms certified5113
def sourceMap5113swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,12,13,14,15,9,10,11] (sourceLabel 7 4 2 v)
def fusedMap5113swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 4 2 v)
theorem sourceMap5113swap_checked : acceptsGraphIso
    (source (graph core5113) (root 7) 4 2) DegreeTwoThreeSpectrum4839.graph sourceMap5113swap=true := by decide +kernel
theorem fusedMap5113swap_checked : acceptsGraphIso
    (fused (graph core5113) (root 7) 4 2) DegreeTwoThreeSpectrum4018.graph fusedMap5113swap=true := by decide +kernel
theorem certified5113swap : Certified (graph core5113) (root 7) 4 2 :=
  of_native_maps core5113 DegreeTwoThreeSpectrum4839.graph DegreeTwoThreeSpectrum4018.graph
    sourceMap5113swap fusedMap5113swap sourceMap5113swap_checked fusedMap5113swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5113
#print axioms sourceMap5113swap_checked
#print axioms fusedMap5113swap_checked
#print axioms certified5113swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
