/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0541 : Family 7 := level7.get ⟨18,by decide⟩
def sourceMap0541 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (sourceLabel 7 1 1 v)
def fusedMap0541 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap0541_checked : acceptsGraphIso
    (source (graph core0541) (root 7) 1 1) DegreeOneSmallSpectrum516.graph sourceMap0541=true := by decide +kernel
theorem fusedMap0541_checked : acceptsGraphIso
    (fused (graph core0541) (root 7) 1 1) DegreeOneSmallSpectrum388.graph fusedMap0541=true := by decide +kernel
theorem certified0541 : Certified (graph core0541) (root 7) 1 1 :=
  of_native_maps core0541 DegreeOneSmallSpectrum516.graph DegreeOneSmallSpectrum388.graph
    sourceMap0541 fusedMap0541 sourceMap0541_checked fusedMap0541_checked
    DegreeOneSmallComparisons.comparison0541
#print axioms sourceMap0541_checked
#print axioms fusedMap0541_checked
#print axioms certified0541
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
