/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5478 : Family 6 := level6.get ⟨40,by decide⟩
def sourceMap5478 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (sourceLabel 6 0 4 v)
def fusedMap5478 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap5478_checked : acceptsGraphIso
    (source (graph core5478) (root 6) 0 4) DegreeOneSmallSpectrum1016.graph sourceMap5478=true := by decide +kernel
theorem fusedMap5478_checked : acceptsGraphIso
    (fused (graph core5478) (root 6) 0 4) DegreeOneSmallSpectrum1021.graph fusedMap5478=true := by decide +kernel
theorem certified5478 : Certified (graph core5478) (root 6) 0 4 :=
  of_native_maps core5478 DegreeOneSmallSpectrum1016.graph DegreeOneSmallSpectrum1021.graph
    sourceMap5478 fusedMap5478 sourceMap5478_checked fusedMap5478_checked
    DegreeTwoThreeFiniteComparisons.comparison5478
#print axioms sourceMap5478_checked
#print axioms fusedMap5478_checked
#print axioms certified5478
def sourceMap5478swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,12,8] (sourceLabel 6 4 0 v)
def fusedMap5478swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap5478swap_checked : acceptsGraphIso
    (source (graph core5478) (root 6) 4 0) DegreeOneSmallSpectrum1016.graph sourceMap5478swap=true := by decide +kernel
theorem fusedMap5478swap_checked : acceptsGraphIso
    (fused (graph core5478) (root 6) 4 0) DegreeOneSmallSpectrum1021.graph fusedMap5478swap=true := by decide +kernel
theorem certified5478swap : Certified (graph core5478) (root 6) 4 0 :=
  of_native_maps core5478 DegreeOneSmallSpectrum1016.graph DegreeOneSmallSpectrum1021.graph
    sourceMap5478swap fusedMap5478swap sourceMap5478swap_checked fusedMap5478swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5478
#print axioms sourceMap5478swap_checked
#print axioms fusedMap5478swap_checked
#print axioms certified5478swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
