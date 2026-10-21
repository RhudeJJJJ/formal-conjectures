/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0489 : Family 7 := level7.get ⟨8,by decide⟩
def sourceMap0489 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9] (sourceLabel 7 0 0 v)
def fusedMap0489 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9] (fusedLabel 7 0 0 v)
theorem sourceMap0489_checked : acceptsGraphIso
    (source (graph core0489) (root 7) 0 0) DegreeOneSmallSpectrum117.graph sourceMap0489=true := by decide +kernel
theorem fusedMap0489_checked : acceptsGraphIso
    (fused (graph core0489) (root 7) 0 0) DegreeOneSmallSpectrum075.graph fusedMap0489=true := by decide +kernel
theorem certified0489 : Certified (graph core0489) (root 7) 0 0 :=
  of_native_maps core0489 DegreeOneSmallSpectrum117.graph DegreeOneSmallSpectrum075.graph
    sourceMap0489 fusedMap0489 sourceMap0489_checked fusedMap0489_checked
    DegreeOneSmallComparisons.comparison0489
#print axioms sourceMap0489_checked
#print axioms fusedMap0489_checked
#print axioms certified0489
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
