/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0461 : Family 7 := level7.get ⟨2,by decide⟩
def sourceMap0461 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,11,8,9,10] (sourceLabel 7 0 2 v)
def fusedMap0461 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0461_checked : acceptsGraphIso
    (source (graph core0461) (root 7) 0 2) DegreeOneSmallSpectrum384.graph sourceMap0461=true := by decide +kernel
theorem fusedMap0461_checked : acceptsGraphIso
    (fused (graph core0461) (root 7) 0 2) DegreeOneSmallSpectrum386.graph fusedMap0461=true := by decide +kernel
theorem certified0461 : Certified (graph core0461) (root 7) 0 2 :=
  of_native_maps core0461 DegreeOneSmallSpectrum384.graph DegreeOneSmallSpectrum386.graph
    sourceMap0461 fusedMap0461 sourceMap0461_checked fusedMap0461_checked
    DegreeOneSmallComparisons.comparison0461
#print axioms sourceMap0461_checked
#print axioms fusedMap0461_checked
#print axioms certified0461
def sourceMap0461swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10,11] (sourceLabel 7 2 0 v)
def fusedMap0461swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0461swap_checked : acceptsGraphIso
    (source (graph core0461) (root 7) 2 0) DegreeOneSmallSpectrum384.graph sourceMap0461swap=true := by decide +kernel
theorem fusedMap0461swap_checked : acceptsGraphIso
    (fused (graph core0461) (root 7) 2 0) DegreeOneSmallSpectrum386.graph fusedMap0461swap=true := by decide +kernel
theorem certified0461swap : Certified (graph core0461) (root 7) 2 0 :=
  of_native_maps core0461 DegreeOneSmallSpectrum384.graph DegreeOneSmallSpectrum386.graph
    sourceMap0461swap fusedMap0461swap sourceMap0461swap_checked fusedMap0461swap_checked
    DegreeOneSmallComparisons.comparison0461
#print axioms sourceMap0461swap_checked
#print axioms fusedMap0461swap_checked
#print axioms certified0461swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
