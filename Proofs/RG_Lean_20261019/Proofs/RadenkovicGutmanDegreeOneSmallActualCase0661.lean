/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0661 : Family 7 := level7.get ⟨52,by decide⟩
def sourceMap0661 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (sourceLabel 7 1 1 v)
def fusedMap0661 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap0661_checked : acceptsGraphIso
    (source (graph core0661) (root 7) 1 1) DegreeOneSmallSpectrum796.graph sourceMap0661=true := by decide +kernel
theorem fusedMap0661_checked : acceptsGraphIso
    (fused (graph core0661) (root 7) 1 1) DegreeOneSmallSpectrum571.graph fusedMap0661=true := by decide +kernel
theorem certified0661 : Certified (graph core0661) (root 7) 1 1 :=
  of_native_maps core0661 DegreeOneSmallSpectrum796.graph DegreeOneSmallSpectrum571.graph
    sourceMap0661 fusedMap0661 sourceMap0661_checked fusedMap0661_checked
    DegreeOneSmallComparisons.comparison0661
#print axioms sourceMap0661_checked
#print axioms fusedMap0661_checked
#print axioms certified0661
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
