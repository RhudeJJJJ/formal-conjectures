/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0613 : Family 7 := level7.get ⟨39,by decide⟩
def sourceMap0613 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 7 1 1 v)
def fusedMap0613 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap0613_checked : acceptsGraphIso
    (source (graph core0613) (root 7) 1 1) DegreeOneSmallSpectrum784.graph sourceMap0613=true := by decide +kernel
theorem fusedMap0613_checked : acceptsGraphIso
    (fused (graph core0613) (root 7) 1 1) DegreeOneSmallSpectrum505.graph fusedMap0613=true := by decide +kernel
theorem certified0613 : Certified (graph core0613) (root 7) 1 1 :=
  of_native_maps core0613 DegreeOneSmallSpectrum784.graph DegreeOneSmallSpectrum505.graph
    sourceMap0613 fusedMap0613 sourceMap0613_checked fusedMap0613_checked
    DegreeOneSmallComparisons.comparison0613
#print axioms sourceMap0613_checked
#print axioms fusedMap0613_checked
#print axioms certified0613
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
