/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2070 : Family 6 := level6.get ⟨17,by decide⟩
def sourceMap2070 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 6 0 4 v)
def fusedMap2070 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap2070_checked : acceptsGraphIso
    (source (graph core2070) (root 6) 0 4) DegreeOneSmallSpectrum969.graph sourceMap2070=true := by decide +kernel
theorem fusedMap2070_checked : acceptsGraphIso
    (fused (graph core2070) (root 6) 0 4) DegreeOneSmallSpectrum971.graph fusedMap2070=true := by decide +kernel
theorem certified2070 : Certified (graph core2070) (root 6) 0 4 :=
  of_native_maps core2070 DegreeOneSmallSpectrum969.graph DegreeOneSmallSpectrum971.graph
    sourceMap2070 fusedMap2070 sourceMap2070_checked fusedMap2070_checked
    DegreeTwoThreeFiniteComparisons.comparison2070
#print axioms sourceMap2070_checked
#print axioms fusedMap2070_checked
#print axioms certified2070
def sourceMap2070swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,8,9,10,11,12,7] (sourceLabel 6 4 0 v)
def fusedMap2070swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap2070swap_checked : acceptsGraphIso
    (source (graph core2070) (root 6) 4 0) DegreeOneSmallSpectrum969.graph sourceMap2070swap=true := by decide +kernel
theorem fusedMap2070swap_checked : acceptsGraphIso
    (fused (graph core2070) (root 6) 4 0) DegreeOneSmallSpectrum971.graph fusedMap2070swap=true := by decide +kernel
theorem certified2070swap : Certified (graph core2070) (root 6) 4 0 :=
  of_native_maps core2070 DegreeOneSmallSpectrum969.graph DegreeOneSmallSpectrum971.graph
    sourceMap2070swap fusedMap2070swap sourceMap2070swap_checked fusedMap2070swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2070
#print axioms sourceMap2070swap_checked
#print axioms fusedMap2070swap_checked
#print axioms certified2070swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
