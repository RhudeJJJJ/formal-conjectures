/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0196 : Family 5 := level5.get ⟨3,by decide⟩
def sourceMap0196 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 2) → Fin 9 :=
  fun v => ![1,0,5,6,7,8,4,2,3] (sourceLabel 5 0 1 v)
def fusedMap0196 : (Vertices 5 ⊕ Fin 3) → Fin 9 :=
  fun v => ![5,0,1,2,3,4,6,7,8] (fusedLabel 5 0 1 v)
theorem sourceMap0196_checked : acceptsGraphIso
    (source (graph core0196) (root 5) 0 1) DegreeOneSmallSpectrum060.graph sourceMap0196=true := by decide +kernel
theorem fusedMap0196_checked : acceptsGraphIso
    (fused (graph core0196) (root 5) 0 1) DegreeOneSmallSpectrum036.graph fusedMap0196=true := by decide +kernel
theorem certified0196 : Certified (graph core0196) (root 5) 0 1 :=
  of_native_maps core0196 DegreeOneSmallSpectrum060.graph DegreeOneSmallSpectrum036.graph
    sourceMap0196 fusedMap0196 sourceMap0196_checked fusedMap0196_checked
    DegreeOneSmallComparisons.comparison0196
#print axioms sourceMap0196_checked
#print axioms fusedMap0196_checked
#print axioms certified0196
def sourceMap0196swap : (Vertices 5 ⊕ Fin 2 ⊕ Fin 1) → Fin 9 :=
  fun v => ![1,0,5,6,7,8,2,3,4] (sourceLabel 5 1 0 v)
def fusedMap0196swap : (Vertices 5 ⊕ Fin 3) → Fin 9 :=
  fun v => ![5,0,1,2,3,4,6,7,8] (fusedLabel 5 1 0 v)
theorem sourceMap0196swap_checked : acceptsGraphIso
    (source (graph core0196) (root 5) 1 0) DegreeOneSmallSpectrum060.graph sourceMap0196swap=true := by decide +kernel
theorem fusedMap0196swap_checked : acceptsGraphIso
    (fused (graph core0196) (root 5) 1 0) DegreeOneSmallSpectrum036.graph fusedMap0196swap=true := by decide +kernel
theorem certified0196swap : Certified (graph core0196) (root 5) 1 0 :=
  of_native_maps core0196 DegreeOneSmallSpectrum060.graph DegreeOneSmallSpectrum036.graph
    sourceMap0196swap fusedMap0196swap sourceMap0196swap_checked fusedMap0196swap_checked
    DegreeOneSmallComparisons.comparison0196
#print axioms sourceMap0196swap_checked
#print axioms fusedMap0196swap_checked
#print axioms certified0196swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
