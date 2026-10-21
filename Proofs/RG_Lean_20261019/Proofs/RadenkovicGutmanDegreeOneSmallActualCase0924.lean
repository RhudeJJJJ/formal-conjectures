/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0924 : Family 8 := level8.get ⟨63,by decide⟩
def sourceMap0924 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,5,4,2,3] (sourceLabel 8 0 1 v)
def fusedMap0924 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (fusedLabel 8 0 1 v)
theorem sourceMap0924_checked : acceptsGraphIso
    (source (graph core0924) (root 8) 0 1) DegreeOneSmallSpectrum545.graph sourceMap0924=true := by decide +kernel
theorem fusedMap0924_checked : acceptsGraphIso
    (fused (graph core0924) (root 8) 0 1) DegreeOneSmallSpectrum550.graph fusedMap0924=true := by decide +kernel
theorem certified0924 : Certified (graph core0924) (root 8) 0 1 :=
  of_native_maps core0924 DegreeOneSmallSpectrum545.graph DegreeOneSmallSpectrum550.graph
    sourceMap0924 fusedMap0924 sourceMap0924_checked fusedMap0924_checked
    DegreeOneSmallComparisons.comparison0924
#print axioms sourceMap0924_checked
#print axioms fusedMap0924_checked
#print axioms certified0924
def sourceMap0924swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,5,2,3,4] (sourceLabel 8 1 0 v)
def fusedMap0924swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (fusedLabel 8 1 0 v)
theorem sourceMap0924swap_checked : acceptsGraphIso
    (source (graph core0924) (root 8) 1 0) DegreeOneSmallSpectrum545.graph sourceMap0924swap=true := by decide +kernel
theorem fusedMap0924swap_checked : acceptsGraphIso
    (fused (graph core0924) (root 8) 1 0) DegreeOneSmallSpectrum550.graph fusedMap0924swap=true := by decide +kernel
theorem certified0924swap : Certified (graph core0924) (root 8) 1 0 :=
  of_native_maps core0924 DegreeOneSmallSpectrum545.graph DegreeOneSmallSpectrum550.graph
    sourceMap0924swap fusedMap0924swap sourceMap0924swap_checked fusedMap0924swap_checked
    DegreeOneSmallComparisons.comparison0924
#print axioms sourceMap0924swap_checked
#print axioms fusedMap0924swap_checked
#print axioms certified0924swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
