/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0489 : Family 10 := level10.get ⟨361,by decide⟩
def sourceMap0489 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,7,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0489 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,7,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0489_checked : acceptsGraphIso
    (source (graph core0489) (root 10) 0 0) DegreeOneSmallSpectrum1376.graph sourceMap0489=true := by decide +kernel
theorem fusedMap0489_checked : acceptsGraphIso
    (fused (graph core0489) (root 10) 0 0) DegreeOneSmallSpectrum1327.graph fusedMap0489=true := by decide +kernel
theorem certified0489 : Certified (graph core0489) (root 10) 0 0 :=
  of_native_maps core0489 DegreeOneSmallSpectrum1376.graph DegreeOneSmallSpectrum1327.graph
    sourceMap0489 fusedMap0489 sourceMap0489_checked fusedMap0489_checked
    DegreeTwoThreeFiniteComparisons.comparison0489
#print axioms sourceMap0489_checked
#print axioms fusedMap0489_checked
#print axioms certified0489
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
