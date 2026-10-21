/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0643 : Family 7 := level7.get ⟨46,by decide⟩
def sourceMap0643 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (sourceLabel 7 1 1 v)
def fusedMap0643 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap0643_checked : acceptsGraphIso
    (source (graph core0643) (root 7) 1 1) DegreeOneSmallSpectrum793.graph sourceMap0643=true := by decide +kernel
theorem fusedMap0643_checked : acceptsGraphIso
    (fused (graph core0643) (root 7) 1 1) DegreeOneSmallSpectrum544.graph fusedMap0643=true := by decide +kernel
theorem certified0643 : Certified (graph core0643) (root 7) 1 1 :=
  of_native_maps core0643 DegreeOneSmallSpectrum793.graph DegreeOneSmallSpectrum544.graph
    sourceMap0643 fusedMap0643 sourceMap0643_checked fusedMap0643_checked
    DegreeOneSmallComparisons.comparison0643
#print axioms sourceMap0643_checked
#print axioms fusedMap0643_checked
#print axioms certified0643
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
