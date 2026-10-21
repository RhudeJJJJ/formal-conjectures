/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0611 : Family 7 := level7.get ⟨39,by decide⟩
def sourceMap0611 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (sourceLabel 7 0 2 v)
def fusedMap0611 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0611_checked : acceptsGraphIso
    (source (graph core0611) (root 7) 0 2) DegreeOneSmallSpectrum504.graph sourceMap0611=true := by decide +kernel
theorem fusedMap0611_checked : acceptsGraphIso
    (fused (graph core0611) (root 7) 0 2) DegreeOneSmallSpectrum505.graph fusedMap0611=true := by decide +kernel
theorem certified0611 : Certified (graph core0611) (root 7) 0 2 :=
  of_native_maps core0611 DegreeOneSmallSpectrum504.graph DegreeOneSmallSpectrum505.graph
    sourceMap0611 fusedMap0611 sourceMap0611_checked fusedMap0611_checked
    DegreeOneSmallComparisons.comparison0611
#print axioms sourceMap0611_checked
#print axioms fusedMap0611_checked
#print axioms certified0611
def sourceMap0611swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 7 2 0 v)
def fusedMap0611swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0611swap_checked : acceptsGraphIso
    (source (graph core0611) (root 7) 2 0) DegreeOneSmallSpectrum504.graph sourceMap0611swap=true := by decide +kernel
theorem fusedMap0611swap_checked : acceptsGraphIso
    (fused (graph core0611) (root 7) 2 0) DegreeOneSmallSpectrum505.graph fusedMap0611swap=true := by decide +kernel
theorem certified0611swap : Certified (graph core0611) (root 7) 2 0 :=
  of_native_maps core0611 DegreeOneSmallSpectrum504.graph DegreeOneSmallSpectrum505.graph
    sourceMap0611swap fusedMap0611swap sourceMap0611swap_checked fusedMap0611swap_checked
    DegreeOneSmallComparisons.comparison0611
#print axioms sourceMap0611swap_checked
#print axioms fusedMap0611swap_checked
#print axioms certified0611swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
