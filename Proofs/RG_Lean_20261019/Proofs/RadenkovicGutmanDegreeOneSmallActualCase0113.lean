/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0113 : Family 4 := level4.get ⟨1,by decide⟩
def sourceMap0113 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 3) → Fin 9 :=
  fun v => ![0,1,2,3,4,8,5,6,7] (sourceLabel 4 0 2 v)
def fusedMap0113 : (Vertices 4 ⊕ Fin 4) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (fusedLabel 4 0 2 v)
theorem sourceMap0113_checked : acceptsGraphIso
    (source (graph core0113) (root 4) 0 2) DegreeOneSmallSpectrum052.graph sourceMap0113=true := by decide +kernel
theorem fusedMap0113_checked : acceptsGraphIso
    (fused (graph core0113) (root 4) 0 2) DegreeOneSmallSpectrum034.graph fusedMap0113=true := by decide +kernel
theorem certified0113 : Certified (graph core0113) (root 4) 0 2 :=
  of_native_maps core0113 DegreeOneSmallSpectrum052.graph DegreeOneSmallSpectrum034.graph
    sourceMap0113 fusedMap0113 sourceMap0113_checked fusedMap0113_checked
    DegreeOneSmallComparisons.comparison0113
#print axioms sourceMap0113_checked
#print axioms fusedMap0113_checked
#print axioms certified0113
def sourceMap0113swap : (Vertices 4 ⊕ Fin 3 ⊕ Fin 1) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (sourceLabel 4 2 0 v)
def fusedMap0113swap : (Vertices 4 ⊕ Fin 4) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (fusedLabel 4 2 0 v)
theorem sourceMap0113swap_checked : acceptsGraphIso
    (source (graph core0113) (root 4) 2 0) DegreeOneSmallSpectrum052.graph sourceMap0113swap=true := by decide +kernel
theorem fusedMap0113swap_checked : acceptsGraphIso
    (fused (graph core0113) (root 4) 2 0) DegreeOneSmallSpectrum034.graph fusedMap0113swap=true := by decide +kernel
theorem certified0113swap : Certified (graph core0113) (root 4) 2 0 :=
  of_native_maps core0113 DegreeOneSmallSpectrum052.graph DegreeOneSmallSpectrum034.graph
    sourceMap0113swap fusedMap0113swap sourceMap0113swap_checked fusedMap0113swap_checked
    DegreeOneSmallComparisons.comparison0113
#print axioms sourceMap0113swap_checked
#print axioms fusedMap0113swap_checked
#print axioms certified0113swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
