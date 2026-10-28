/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5055 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap5055 : (Vertices 2 ⊕ Fin 3 ⊕ Fin 5) → Fin 11 :=
  fun v => ![1,5,6,2,3,4,0,7,8,9,10] (sourceLabel 2 2 4 v)
def fusedMap5055 : (Vertices 2 ⊕ Fin 8) → Fin 11 :=
  fun v => ![3,4,5,2,1,0,6,7,8,9,10] (fusedLabel 2 2 4 v)
theorem sourceMap5055_checked : acceptsGraphIso
    (source (graph core5055) (root 2) 2 4) DegreeOneSmallSpectrum225.graph sourceMap5055=true := by decide +kernel
theorem fusedMap5055_checked : acceptsGraphIso
    (fused (graph core5055) (root 2) 2 4) DegreeOneSmallSpectrum164.graph fusedMap5055=true := by decide +kernel
theorem certified5055 : Certified (graph core5055) (root 2) 2 4 :=
  of_native_maps core5055 DegreeOneSmallSpectrum225.graph DegreeOneSmallSpectrum164.graph
    sourceMap5055 fusedMap5055 sourceMap5055_checked fusedMap5055_checked
    DegreeTwoThreeFiniteComparisons.comparison5055
#print axioms sourceMap5055_checked
#print axioms fusedMap5055_checked
#print axioms certified5055
def sourceMap5055swap : (Vertices 2 ⊕ Fin 5 ⊕ Fin 3) → Fin 11 :=
  fun v => ![1,5,6,0,7,8,9,10,2,3,4] (sourceLabel 2 4 2 v)
def fusedMap5055swap : (Vertices 2 ⊕ Fin 8) → Fin 11 :=
  fun v => ![3,4,5,2,1,0,6,7,8,9,10] (fusedLabel 2 4 2 v)
theorem sourceMap5055swap_checked : acceptsGraphIso
    (source (graph core5055) (root 2) 4 2) DegreeOneSmallSpectrum225.graph sourceMap5055swap=true := by decide +kernel
theorem fusedMap5055swap_checked : acceptsGraphIso
    (fused (graph core5055) (root 2) 4 2) DegreeOneSmallSpectrum164.graph fusedMap5055swap=true := by decide +kernel
theorem certified5055swap : Certified (graph core5055) (root 2) 4 2 :=
  of_native_maps core5055 DegreeOneSmallSpectrum225.graph DegreeOneSmallSpectrum164.graph
    sourceMap5055swap fusedMap5055swap sourceMap5055swap_checked fusedMap5055swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5055
#print axioms sourceMap5055swap_checked
#print axioms fusedMap5055swap_checked
#print axioms certified5055swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
