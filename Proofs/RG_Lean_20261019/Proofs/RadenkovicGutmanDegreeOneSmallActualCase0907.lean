/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0907 : Family 8 := level8.get ⟨58,by decide⟩
def sourceMap0907 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,5,6,7,8,9,10,3,4] (sourceLabel 8 0 0 v)
def fusedMap0907 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0907_checked : acceptsGraphIso
    (source (graph core0907) (root 8) 0 0) DegreeOneSmallSpectrum309.graph sourceMap0907=true := by decide +kernel
theorem fusedMap0907_checked : acceptsGraphIso
    (fused (graph core0907) (root 8) 0 0) DegreeOneSmallSpectrum204.graph fusedMap0907=true := by decide +kernel
theorem certified0907 : Certified (graph core0907) (root 8) 0 0 :=
  of_native_maps core0907 DegreeOneSmallSpectrum309.graph DegreeOneSmallSpectrum204.graph
    sourceMap0907 fusedMap0907 sourceMap0907_checked fusedMap0907_checked
    DegreeOneSmallComparisons.comparison0907
#print axioms sourceMap0907_checked
#print axioms fusedMap0907_checked
#print axioms certified0907
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
