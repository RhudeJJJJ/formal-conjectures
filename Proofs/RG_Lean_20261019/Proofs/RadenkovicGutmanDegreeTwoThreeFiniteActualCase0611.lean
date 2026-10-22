/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0611 : Family 10 := level10.get ⟨722,by decide⟩
def sourceMap0611 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0611 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0611_checked : acceptsGraphIso
    (source (graph core0611) (root 10) 0 0) DegreeOneSmallSpectrum1128.graph sourceMap0611=true := by decide +kernel
theorem fusedMap0611_checked : acceptsGraphIso
    (fused (graph core0611) (root 10) 0 0) DegreeOneSmallSpectrum1105.graph fusedMap0611=true := by decide +kernel
theorem certified0611 : Certified (graph core0611) (root 10) 0 0 :=
  of_native_maps core0611 DegreeOneSmallSpectrum1128.graph DegreeOneSmallSpectrum1105.graph
    sourceMap0611 fusedMap0611 sourceMap0611_checked fusedMap0611_checked
    DegreeTwoThreeFiniteComparisons.comparison0611
#print axioms sourceMap0611_checked
#print axioms fusedMap0611_checked
#print axioms certified0611
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
