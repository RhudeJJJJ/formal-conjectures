/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0132 : Family 4 := level4.get ⟨2,by decide⟩
def sourceMap0132 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (sourceLabel 4 0 5 v)
def fusedMap0132 : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11] (fusedLabel 4 0 5 v)
theorem sourceMap0132_checked : acceptsGraphIso
    (source (graph core0132) (root 4) 0 5) DegreeOneSmallSpectrum381.graph sourceMap0132=true := by decide +kernel
theorem fusedMap0132_checked : acceptsGraphIso
    (fused (graph core0132) (root 4) 0 5) DegreeOneSmallSpectrum386.graph fusedMap0132=true := by decide +kernel
theorem certified0132 : Certified (graph core0132) (root 4) 0 5 :=
  of_native_maps core0132 DegreeOneSmallSpectrum381.graph DegreeOneSmallSpectrum386.graph
    sourceMap0132 fusedMap0132 sourceMap0132_checked fusedMap0132_checked
    DegreeOneSmallComparisons.comparison0132
#print axioms sourceMap0132_checked
#print axioms fusedMap0132_checked
#print axioms certified0132
def sourceMap0132swap : (Vertices 4 ⊕ Fin 6 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,2,3,4,5,0,7,8,9,10,11,6] (sourceLabel 4 5 0 v)
def fusedMap0132swap : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11] (fusedLabel 4 5 0 v)
theorem sourceMap0132swap_checked : acceptsGraphIso
    (source (graph core0132) (root 4) 5 0) DegreeOneSmallSpectrum381.graph sourceMap0132swap=true := by decide +kernel
theorem fusedMap0132swap_checked : acceptsGraphIso
    (fused (graph core0132) (root 4) 5 0) DegreeOneSmallSpectrum386.graph fusedMap0132swap=true := by decide +kernel
theorem certified0132swap : Certified (graph core0132) (root 4) 5 0 :=
  of_native_maps core0132 DegreeOneSmallSpectrum381.graph DegreeOneSmallSpectrum386.graph
    sourceMap0132swap fusedMap0132swap sourceMap0132swap_checked fusedMap0132swap_checked
    DegreeOneSmallComparisons.comparison0132
#print axioms sourceMap0132swap_checked
#print axioms fusedMap0132swap_checked
#print axioms certified0132swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
