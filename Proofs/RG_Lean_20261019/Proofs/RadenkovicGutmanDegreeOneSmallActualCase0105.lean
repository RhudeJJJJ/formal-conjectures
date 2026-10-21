/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0105 : Family 4 := level4.get ⟨0,by decide⟩
def sourceMap0105 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 4 1 4 v)
def fusedMap0105 : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9,10,11] (fusedLabel 4 1 4 v)
theorem sourceMap0105_checked : acceptsGraphIso
    (source (graph core0105) (root 4) 1 4) DegreeOneSmallSpectrum393.graph sourceMap0105=true := by decide +kernel
theorem fusedMap0105_checked : acceptsGraphIso
    (fused (graph core0105) (root 4) 1 4) DegreeOneSmallSpectrum369.graph fusedMap0105=true := by decide +kernel
theorem certified0105 : Certified (graph core0105) (root 4) 1 4 :=
  of_native_maps core0105 DegreeOneSmallSpectrum393.graph DegreeOneSmallSpectrum369.graph
    sourceMap0105 fusedMap0105 sourceMap0105_checked fusedMap0105_checked
    DegreeOneSmallComparisons.comparison0105
#print axioms sourceMap0105_checked
#print axioms fusedMap0105_checked
#print axioms certified0105
def sourceMap0105swap : (Vertices 4 ⊕ Fin 5 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,7,8,9,10,11,5,6] (sourceLabel 4 4 1 v)
def fusedMap0105swap : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9,10,11] (fusedLabel 4 4 1 v)
theorem sourceMap0105swap_checked : acceptsGraphIso
    (source (graph core0105) (root 4) 4 1) DegreeOneSmallSpectrum393.graph sourceMap0105swap=true := by decide +kernel
theorem fusedMap0105swap_checked : acceptsGraphIso
    (fused (graph core0105) (root 4) 4 1) DegreeOneSmallSpectrum369.graph fusedMap0105swap=true := by decide +kernel
theorem certified0105swap : Certified (graph core0105) (root 4) 4 1 :=
  of_native_maps core0105 DegreeOneSmallSpectrum393.graph DegreeOneSmallSpectrum369.graph
    sourceMap0105swap fusedMap0105swap sourceMap0105swap_checked fusedMap0105swap_checked
    DegreeOneSmallComparisons.comparison0105
#print axioms sourceMap0105swap_checked
#print axioms fusedMap0105swap_checked
#print axioms certified0105swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
