/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0151 : Family 4 := level4.get ⟨4,by decide⟩
def sourceMap0151 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (sourceLabel 4 1 2 v)
def fusedMap0151 : (Vertices 4 ⊕ Fin 5) → Fin 10 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9] (fusedLabel 4 1 2 v)
theorem sourceMap0151_checked : acceptsGraphIso
    (source (graph core0151) (root 4) 1 2) DegreeOneSmallSpectrum097.graph sourceMap0151=true := by decide +kernel
theorem fusedMap0151_checked : acceptsGraphIso
    (fused (graph core0151) (root 4) 1 2) DegreeOneSmallSpectrum074.graph fusedMap0151=true := by decide +kernel
theorem certified0151 : Certified (graph core0151) (root 4) 1 2 :=
  of_native_maps core0151 DegreeOneSmallSpectrum097.graph DegreeOneSmallSpectrum074.graph
    sourceMap0151 fusedMap0151 sourceMap0151_checked fusedMap0151_checked
    DegreeOneSmallComparisons.comparison0151
#print axioms sourceMap0151_checked
#print axioms fusedMap0151_checked
#print axioms certified0151
def sourceMap0151swap : (Vertices 4 ⊕ Fin 3 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,1,2,3,4,7,8,9,5,6] (sourceLabel 4 2 1 v)
def fusedMap0151swap : (Vertices 4 ⊕ Fin 5) → Fin 10 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9] (fusedLabel 4 2 1 v)
theorem sourceMap0151swap_checked : acceptsGraphIso
    (source (graph core0151) (root 4) 2 1) DegreeOneSmallSpectrum097.graph sourceMap0151swap=true := by decide +kernel
theorem fusedMap0151swap_checked : acceptsGraphIso
    (fused (graph core0151) (root 4) 2 1) DegreeOneSmallSpectrum074.graph fusedMap0151swap=true := by decide +kernel
theorem certified0151swap : Certified (graph core0151) (root 4) 2 1 :=
  of_native_maps core0151 DegreeOneSmallSpectrum097.graph DegreeOneSmallSpectrum074.graph
    sourceMap0151swap fusedMap0151swap sourceMap0151swap_checked fusedMap0151swap_checked
    DegreeOneSmallComparisons.comparison0151
#print axioms sourceMap0151swap_checked
#print axioms fusedMap0151swap_checked
#print axioms certified0151swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
