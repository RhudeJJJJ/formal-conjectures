/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0044 : Family 2 := level2.get ⟨0,by decide⟩
def sourceMap0044 : (Vertices 2 ⊕ Fin 2 ⊕ Fin 7) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11] (sourceLabel 2 1 6 v)
def fusedMap0044 : (Vertices 2 ⊕ Fin 9) → Fin 12 :=
  fun v => ![3,4,5,2,1,0,6,7,8,9,10,11] (fusedLabel 2 1 6 v)
theorem sourceMap0044_checked : acceptsGraphIso
    (source (graph core0044) (root 2) 1 6) DegreeOneSmallSpectrum379.graph sourceMap0044=true := by decide +kernel
theorem fusedMap0044_checked : acceptsGraphIso
    (fused (graph core0044) (root 2) 1 6) DegreeOneSmallSpectrum369.graph fusedMap0044=true := by decide +kernel
theorem certified0044 : Certified (graph core0044) (root 2) 1 6 :=
  of_native_maps core0044 DegreeOneSmallSpectrum379.graph DegreeOneSmallSpectrum369.graph
    sourceMap0044 fusedMap0044 sourceMap0044_checked fusedMap0044_checked
    DegreeOneSmallComparisons.comparison0044
#print axioms sourceMap0044_checked
#print axioms fusedMap0044_checked
#print axioms certified0044
def sourceMap0044swap : (Vertices 2 ⊕ Fin 7 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,3,4,1,0,7,8,9,10,11,5,6] (sourceLabel 2 6 1 v)
def fusedMap0044swap : (Vertices 2 ⊕ Fin 9) → Fin 12 :=
  fun v => ![3,4,5,2,1,0,6,7,8,9,10,11] (fusedLabel 2 6 1 v)
theorem sourceMap0044swap_checked : acceptsGraphIso
    (source (graph core0044) (root 2) 6 1) DegreeOneSmallSpectrum379.graph sourceMap0044swap=true := by decide +kernel
theorem fusedMap0044swap_checked : acceptsGraphIso
    (fused (graph core0044) (root 2) 6 1) DegreeOneSmallSpectrum369.graph fusedMap0044swap=true := by decide +kernel
theorem certified0044swap : Certified (graph core0044) (root 2) 6 1 :=
  of_native_maps core0044 DegreeOneSmallSpectrum379.graph DegreeOneSmallSpectrum369.graph
    sourceMap0044swap fusedMap0044swap sourceMap0044swap_checked fusedMap0044swap_checked
    DegreeOneSmallComparisons.comparison0044
#print axioms sourceMap0044swap_checked
#print axioms fusedMap0044swap_checked
#print axioms certified0044swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
