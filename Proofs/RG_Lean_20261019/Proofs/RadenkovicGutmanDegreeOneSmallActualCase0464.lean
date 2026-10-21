/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0464 : Family 7 := level7.get ⟨2,by decide⟩
def sourceMap0464 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,8,9,10] (sourceLabel 7 1 2 v)
def fusedMap0464 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0464_checked : acceptsGraphIso
    (source (graph core0464) (root 7) 1 2) DegreeOneSmallSpectrum937.graph sourceMap0464=true := by decide +kernel
theorem fusedMap0464_checked : acceptsGraphIso
    (fused (graph core0464) (root 7) 1 2) DegreeOneSmallSpectrum857.graph fusedMap0464=true := by decide +kernel
theorem certified0464 : Certified (graph core0464) (root 7) 1 2 :=
  of_native_maps core0464 DegreeOneSmallSpectrum937.graph DegreeOneSmallSpectrum857.graph
    sourceMap0464 fusedMap0464 sourceMap0464_checked fusedMap0464_checked
    DegreeOneSmallComparisons.comparison0464
#print axioms sourceMap0464_checked
#print axioms fusedMap0464_checked
#print axioms certified0464
def sourceMap0464swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10,11,12] (sourceLabel 7 2 1 v)
def fusedMap0464swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0464swap_checked : acceptsGraphIso
    (source (graph core0464) (root 7) 2 1) DegreeOneSmallSpectrum937.graph sourceMap0464swap=true := by decide +kernel
theorem fusedMap0464swap_checked : acceptsGraphIso
    (fused (graph core0464) (root 7) 2 1) DegreeOneSmallSpectrum857.graph fusedMap0464swap=true := by decide +kernel
theorem certified0464swap : Certified (graph core0464) (root 7) 2 1 :=
  of_native_maps core0464 DegreeOneSmallSpectrum937.graph DegreeOneSmallSpectrum857.graph
    sourceMap0464swap fusedMap0464swap sourceMap0464swap_checked fusedMap0464swap_checked
    DegreeOneSmallComparisons.comparison0464
#print axioms sourceMap0464swap_checked
#print axioms fusedMap0464swap_checked
#print axioms certified0464swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
