/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0008 : Family 1 := level1.get ⟨0,by decide⟩
def sourceMap0008 : (Vertices 1 ⊕ Fin 1 ⊕ Fin 9) → Fin 12 :=
  fun v => ![4,5,6,3,2,1,0,7,8,9,10,11] (sourceLabel 1 0 8 v)
def fusedMap0008 : (Vertices 1 ⊕ Fin 10) → Fin 12 :=
  fun v => ![4,5,3,2,1,0,6,7,8,9,10,11] (fusedLabel 1 0 8 v)
theorem sourceMap0008_checked : acceptsGraphIso
    (source (graph core0008) (root 1) 0 8) DegreeOneSmallSpectrum378.graph sourceMap0008=true := by decide +kernel
theorem fusedMap0008_checked : acceptsGraphIso
    (fused (graph core0008) (root 1) 0 8) DegreeOneSmallSpectrum369.graph fusedMap0008=true := by decide +kernel
theorem certified0008 : Certified (graph core0008) (root 1) 0 8 :=
  of_native_maps core0008 DegreeOneSmallSpectrum378.graph DegreeOneSmallSpectrum369.graph
    sourceMap0008 fusedMap0008 sourceMap0008_checked fusedMap0008_checked
    DegreeOneSmallComparisons.comparison0008
#print axioms sourceMap0008_checked
#print axioms fusedMap0008_checked
#print axioms certified0008
def sourceMap0008swap : (Vertices 1 ⊕ Fin 9 ⊕ Fin 1) → Fin 12 :=
  fun v => ![4,5,3,2,1,0,7,8,9,10,11,6] (sourceLabel 1 8 0 v)
def fusedMap0008swap : (Vertices 1 ⊕ Fin 10) → Fin 12 :=
  fun v => ![4,5,3,2,1,0,6,7,8,9,10,11] (fusedLabel 1 8 0 v)
theorem sourceMap0008swap_checked : acceptsGraphIso
    (source (graph core0008) (root 1) 8 0) DegreeOneSmallSpectrum378.graph sourceMap0008swap=true := by decide +kernel
theorem fusedMap0008swap_checked : acceptsGraphIso
    (fused (graph core0008) (root 1) 8 0) DegreeOneSmallSpectrum369.graph fusedMap0008swap=true := by decide +kernel
theorem certified0008swap : Certified (graph core0008) (root 1) 8 0 :=
  of_native_maps core0008 DegreeOneSmallSpectrum378.graph DegreeOneSmallSpectrum369.graph
    sourceMap0008swap fusedMap0008swap sourceMap0008swap_checked fusedMap0008swap_checked
    DegreeOneSmallComparisons.comparison0008
#print axioms sourceMap0008swap_checked
#print axioms fusedMap0008swap_checked
#print axioms certified0008swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
