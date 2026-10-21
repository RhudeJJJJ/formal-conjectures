/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0235 : Family 5 := level5.get ⟨8,by decide⟩
def sourceMap0235 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (sourceLabel 5 0 4 v)
def fusedMap0235 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 0 4 v)
theorem sourceMap0235_checked : acceptsGraphIso
    (source (graph core0235) (root 5) 0 4) DegreeOneSmallSpectrum510.graph sourceMap0235=true := by decide +kernel
theorem fusedMap0235_checked : acceptsGraphIso
    (fused (graph core0235) (root 5) 0 4) DegreeOneSmallSpectrum379.graph fusedMap0235=true := by decide +kernel
theorem certified0235 : Certified (graph core0235) (root 5) 0 4 :=
  of_native_maps core0235 DegreeOneSmallSpectrum510.graph DegreeOneSmallSpectrum379.graph
    sourceMap0235 fusedMap0235 sourceMap0235_checked fusedMap0235_checked
    DegreeOneSmallComparisons.comparison0235
#print axioms sourceMap0235_checked
#print axioms fusedMap0235_checked
#print axioms certified0235
def sourceMap0235swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,8,9,10,11,7] (sourceLabel 5 4 0 v)
def fusedMap0235swap : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 4 0 v)
theorem sourceMap0235swap_checked : acceptsGraphIso
    (source (graph core0235) (root 5) 4 0) DegreeOneSmallSpectrum510.graph sourceMap0235swap=true := by decide +kernel
theorem fusedMap0235swap_checked : acceptsGraphIso
    (fused (graph core0235) (root 5) 4 0) DegreeOneSmallSpectrum379.graph fusedMap0235swap=true := by decide +kernel
theorem certified0235swap : Certified (graph core0235) (root 5) 4 0 :=
  of_native_maps core0235 DegreeOneSmallSpectrum510.graph DegreeOneSmallSpectrum379.graph
    sourceMap0235swap fusedMap0235swap sourceMap0235swap_checked fusedMap0235swap_checked
    DegreeOneSmallComparisons.comparison0235
#print axioms sourceMap0235swap_checked
#print axioms fusedMap0235swap_checked
#print axioms certified0235swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
