/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0676 : Family 10 := level10.get ⟨905,by decide⟩
def sourceMap0676 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,6,7,8,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0676 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0676_checked : acceptsGraphIso
    (source (graph core0676) (root 10) 0 0) DegreeOneSmallSpectrum1629.graph sourceMap0676=true := by decide +kernel
theorem fusedMap0676_checked : acceptsGraphIso
    (fused (graph core0676) (root 10) 0 0) DegreeOneSmallSpectrum1407.graph fusedMap0676=true := by decide +kernel
theorem certified0676 : Certified (graph core0676) (root 10) 0 0 :=
  of_native_maps core0676 DegreeOneSmallSpectrum1629.graph DegreeOneSmallSpectrum1407.graph
    sourceMap0676 fusedMap0676 sourceMap0676_checked fusedMap0676_checked
    DegreeTwoThreeFiniteComparisons.comparison0676
#print axioms sourceMap0676_checked
#print axioms fusedMap0676_checked
#print axioms certified0676
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
