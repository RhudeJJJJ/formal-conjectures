/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0944 : Family 8 := level8.get ⟨72,by decide⟩
def sourceMap0944 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,4,2,3] (sourceLabel 8 0 1 v)
def fusedMap0944 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap0944_checked : acceptsGraphIso
    (source (graph core0944) (root 8) 0 1) DegreeOneSmallSpectrum554.graph sourceMap0944=true := by decide +kernel
theorem fusedMap0944_checked : acceptsGraphIso
    (fused (graph core0944) (root 8) 0 1) DegreeOneSmallSpectrum571.graph fusedMap0944=true := by decide +kernel
theorem certified0944 : Certified (graph core0944) (root 8) 0 1 :=
  of_native_maps core0944 DegreeOneSmallSpectrum554.graph DegreeOneSmallSpectrum571.graph
    sourceMap0944 fusedMap0944 sourceMap0944_checked fusedMap0944_checked
    DegreeOneSmallComparisons.comparison0944
#print axioms sourceMap0944_checked
#print axioms fusedMap0944_checked
#print axioms certified0944
def sourceMap0944swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,2,3,4] (sourceLabel 8 1 0 v)
def fusedMap0944swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap0944swap_checked : acceptsGraphIso
    (source (graph core0944) (root 8) 1 0) DegreeOneSmallSpectrum554.graph sourceMap0944swap=true := by decide +kernel
theorem fusedMap0944swap_checked : acceptsGraphIso
    (fused (graph core0944) (root 8) 1 0) DegreeOneSmallSpectrum571.graph fusedMap0944swap=true := by decide +kernel
theorem certified0944swap : Certified (graph core0944) (root 8) 1 0 :=
  of_native_maps core0944 DegreeOneSmallSpectrum554.graph DegreeOneSmallSpectrum571.graph
    sourceMap0944swap fusedMap0944swap sourceMap0944swap_checked fusedMap0944swap_checked
    DegreeOneSmallComparisons.comparison0944
#print axioms sourceMap0944swap_checked
#print axioms fusedMap0944swap_checked
#print axioms certified0944swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
