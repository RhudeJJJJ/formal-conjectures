/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0511 : Family 7 := level7.get ⟨12,by decide⟩
def sourceMap0511 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (sourceLabel 7 1 1 v)
def fusedMap0511 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap0511_checked : acceptsGraphIso
    (source (graph core0511) (root 7) 1 1) DegreeOneSmallSpectrum511.graph sourceMap0511=true := by decide +kernel
theorem fusedMap0511_checked : acceptsGraphIso
    (fused (graph core0511) (root 7) 1 1) DegreeOneSmallSpectrum379.graph fusedMap0511=true := by decide +kernel
theorem certified0511 : Certified (graph core0511) (root 7) 1 1 :=
  of_native_maps core0511 DegreeOneSmallSpectrum511.graph DegreeOneSmallSpectrum379.graph
    sourceMap0511 fusedMap0511 sourceMap0511_checked fusedMap0511_checked
    DegreeOneSmallComparisons.comparison0511
#print axioms sourceMap0511_checked
#print axioms fusedMap0511_checked
#print axioms certified0511
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
