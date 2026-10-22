/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2055 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap2055 : (Vertices 2 ⊕ Fin 1 ⊕ Fin 5) → Fin 9 :=
  fun v => ![2,3,4,5,1,0,6,7,8] (sourceLabel 2 0 4 v)
def fusedMap2055 : (Vertices 2 ⊕ Fin 6) → Fin 9 :=
  fun v => ![2,3,4,1,0,5,6,7,8] (fusedLabel 2 0 4 v)
theorem sourceMap2055_checked : acceptsGraphIso
    (source (graph core2055) (root 2) 0 4) DegreeOneSmallSpectrum042.graph sourceMap2055=true := by decide +kernel
theorem fusedMap2055_checked : acceptsGraphIso
    (fused (graph core2055) (root 2) 0 4) DegreeOneSmallSpectrum034.graph fusedMap2055=true := by decide +kernel
theorem certified2055 : Certified (graph core2055) (root 2) 0 4 :=
  of_native_maps core2055 DegreeOneSmallSpectrum042.graph DegreeOneSmallSpectrum034.graph
    sourceMap2055 fusedMap2055 sourceMap2055_checked fusedMap2055_checked
    DegreeTwoThreeFiniteComparisons.comparison2055
#print axioms sourceMap2055_checked
#print axioms fusedMap2055_checked
#print axioms certified2055
def sourceMap2055swap : (Vertices 2 ⊕ Fin 5 ⊕ Fin 1) → Fin 9 :=
  fun v => ![2,3,4,1,0,6,7,8,5] (sourceLabel 2 4 0 v)
def fusedMap2055swap : (Vertices 2 ⊕ Fin 6) → Fin 9 :=
  fun v => ![2,3,4,1,0,5,6,7,8] (fusedLabel 2 4 0 v)
theorem sourceMap2055swap_checked : acceptsGraphIso
    (source (graph core2055) (root 2) 4 0) DegreeOneSmallSpectrum042.graph sourceMap2055swap=true := by decide +kernel
theorem fusedMap2055swap_checked : acceptsGraphIso
    (fused (graph core2055) (root 2) 4 0) DegreeOneSmallSpectrum034.graph fusedMap2055swap=true := by decide +kernel
theorem certified2055swap : Certified (graph core2055) (root 2) 4 0 :=
  of_native_maps core2055 DegreeOneSmallSpectrum042.graph DegreeOneSmallSpectrum034.graph
    sourceMap2055swap fusedMap2055swap sourceMap2055swap_checked fusedMap2055swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2055
#print axioms sourceMap2055swap_checked
#print axioms fusedMap2055swap_checked
#print axioms certified2055swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
