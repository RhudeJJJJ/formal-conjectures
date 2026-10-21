/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0016 : Family 1 := level1.get ⟨0,by decide⟩
def sourceMap0016 : (Vertices 1 ⊕ Fin 2 ⊕ Fin 8) → Fin 12 :=
  fun v => ![3,6,4,5,2,1,0,7,8,9,10,11] (sourceLabel 1 1 7 v)
def fusedMap0016 : (Vertices 1 ⊕ Fin 10) → Fin 12 :=
  fun v => ![4,5,3,2,1,0,6,7,8,9,10,11] (fusedLabel 1 1 7 v)
theorem sourceMap0016_checked : acceptsGraphIso
    (source (graph core0016) (root 1) 1 7) DegreeOneSmallSpectrum386.graph sourceMap0016=true := by decide +kernel
theorem fusedMap0016_checked : acceptsGraphIso
    (fused (graph core0016) (root 1) 1 7) DegreeOneSmallSpectrum369.graph fusedMap0016=true := by decide +kernel
theorem certified0016 : Certified (graph core0016) (root 1) 1 7 :=
  of_native_maps core0016 DegreeOneSmallSpectrum386.graph DegreeOneSmallSpectrum369.graph
    sourceMap0016 fusedMap0016 sourceMap0016_checked fusedMap0016_checked
    DegreeOneSmallComparisons.comparison0016
#print axioms sourceMap0016_checked
#print axioms fusedMap0016_checked
#print axioms certified0016
def sourceMap0016swap : (Vertices 1 ⊕ Fin 8 ⊕ Fin 2) → Fin 12 :=
  fun v => ![3,6,2,1,0,7,8,9,10,11,4,5] (sourceLabel 1 7 1 v)
def fusedMap0016swap : (Vertices 1 ⊕ Fin 10) → Fin 12 :=
  fun v => ![4,5,3,2,1,0,6,7,8,9,10,11] (fusedLabel 1 7 1 v)
theorem sourceMap0016swap_checked : acceptsGraphIso
    (source (graph core0016) (root 1) 7 1) DegreeOneSmallSpectrum386.graph sourceMap0016swap=true := by decide +kernel
theorem fusedMap0016swap_checked : acceptsGraphIso
    (fused (graph core0016) (root 1) 7 1) DegreeOneSmallSpectrum369.graph fusedMap0016swap=true := by decide +kernel
theorem certified0016swap : Certified (graph core0016) (root 1) 7 1 :=
  of_native_maps core0016 DegreeOneSmallSpectrum386.graph DegreeOneSmallSpectrum369.graph
    sourceMap0016swap fusedMap0016swap sourceMap0016swap_checked fusedMap0016swap_checked
    DegreeOneSmallComparisons.comparison0016
#print axioms sourceMap0016swap_checked
#print axioms fusedMap0016swap_checked
#print axioms certified0016swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
