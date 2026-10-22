/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3084 : Family 5 := level5.get ⟨11,by decide⟩
def sourceMap3084 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (sourceLabel 5 0 5 v)
def fusedMap3084 : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 0 5 v)
theorem sourceMap3084_checked : acceptsGraphIso
    (source (graph core3084) (root 5) 0 5) DegreeOneSmallSpectrum947.graph sourceMap3084=true := by decide +kernel
theorem fusedMap3084_checked : acceptsGraphIso
    (fused (graph core3084) (root 5) 0 5) DegreeOneSmallSpectrum951.graph fusedMap3084=true := by decide +kernel
theorem certified3084 : Certified (graph core3084) (root 5) 0 5 :=
  of_native_maps core3084 DegreeOneSmallSpectrum947.graph DegreeOneSmallSpectrum951.graph
    sourceMap3084 fusedMap3084 sourceMap3084_checked fusedMap3084_checked
    DegreeTwoThreeFiniteComparisons.comparison3084
#print axioms sourceMap3084_checked
#print axioms fusedMap3084_checked
#print axioms certified3084
def sourceMap3084swap : (Vertices 5 ⊕ Fin 6 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,8,9,10,11,12,7] (sourceLabel 5 5 0 v)
def fusedMap3084swap : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 5 0 v)
theorem sourceMap3084swap_checked : acceptsGraphIso
    (source (graph core3084) (root 5) 5 0) DegreeOneSmallSpectrum947.graph sourceMap3084swap=true := by decide +kernel
theorem fusedMap3084swap_checked : acceptsGraphIso
    (fused (graph core3084) (root 5) 5 0) DegreeOneSmallSpectrum951.graph fusedMap3084swap=true := by decide +kernel
theorem certified3084swap : Certified (graph core3084) (root 5) 5 0 :=
  of_native_maps core3084 DegreeOneSmallSpectrum947.graph DegreeOneSmallSpectrum951.graph
    sourceMap3084swap fusedMap3084swap sourceMap3084swap_checked fusedMap3084swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3084
#print axioms sourceMap3084swap_checked
#print axioms fusedMap3084swap_checked
#print axioms certified3084swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
