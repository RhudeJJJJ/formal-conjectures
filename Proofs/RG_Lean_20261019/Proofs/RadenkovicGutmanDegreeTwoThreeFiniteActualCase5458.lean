/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5458 : Family 4 := level4.get ⟨7,by decide⟩
def sourceMap5458 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 3) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (sourceLabel 4 0 2 v)
def fusedMap5458 : (Vertices 4 ⊕ Fin 4) → Fin 9 :=
  fun v => ![1,2,3,4,5,0,6,7,8] (fusedLabel 4 0 2 v)
theorem sourceMap5458_checked : acceptsGraphIso
    (source (graph core5458) (root 4) 0 2) SmallGeFourSpectrum007.graph sourceMap5458=true := by decide +kernel
theorem fusedMap5458_checked : acceptsGraphIso
    (fused (graph core5458) (root 4) 0 2) DegreeOneSmallSpectrum058.graph fusedMap5458=true := by decide +kernel
theorem certified5458 : Certified (graph core5458) (root 4) 0 2 :=
  of_native_maps core5458 SmallGeFourSpectrum007.graph DegreeOneSmallSpectrum058.graph
    sourceMap5458 fusedMap5458 sourceMap5458_checked fusedMap5458_checked
    DegreeTwoThreeFiniteComparisons.comparison5458
#print axioms sourceMap5458_checked
#print axioms fusedMap5458_checked
#print axioms certified5458
def sourceMap5458swap : (Vertices 4 ⊕ Fin 3 ⊕ Fin 1) → Fin 9 :=
  fun v => ![0,1,2,3,4,6,7,8,5] (sourceLabel 4 2 0 v)
def fusedMap5458swap : (Vertices 4 ⊕ Fin 4) → Fin 9 :=
  fun v => ![1,2,3,4,5,0,6,7,8] (fusedLabel 4 2 0 v)
theorem sourceMap5458swap_checked : acceptsGraphIso
    (source (graph core5458) (root 4) 2 0) SmallGeFourSpectrum007.graph sourceMap5458swap=true := by decide +kernel
theorem fusedMap5458swap_checked : acceptsGraphIso
    (fused (graph core5458) (root 4) 2 0) DegreeOneSmallSpectrum058.graph fusedMap5458swap=true := by decide +kernel
theorem certified5458swap : Certified (graph core5458) (root 4) 2 0 :=
  of_native_maps core5458 SmallGeFourSpectrum007.graph DegreeOneSmallSpectrum058.graph
    sourceMap5458swap fusedMap5458swap sourceMap5458swap_checked fusedMap5458swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5458
#print axioms sourceMap5458swap_checked
#print axioms fusedMap5458swap_checked
#print axioms certified5458swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
