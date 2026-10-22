/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0578 : Family 10 := level10.get ⟨635,by decide⟩
def sourceMap0578 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0578 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0578_checked : acceptsGraphIso
    (source (graph core0578) (root 10) 0 0) DegreeOneSmallSpectrum1684.graph sourceMap0578=true := by decide +kernel
theorem fusedMap0578_checked : acceptsGraphIso
    (fused (graph core0578) (root 10) 0 0) DegreeOneSmallSpectrum1214.graph fusedMap0578=true := by decide +kernel
theorem certified0578 : Certified (graph core0578) (root 10) 0 0 :=
  of_native_maps core0578 DegreeOneSmallSpectrum1684.graph DegreeOneSmallSpectrum1214.graph
    sourceMap0578 fusedMap0578 sourceMap0578_checked fusedMap0578_checked
    DegreeTwoThreeFiniteComparisons.comparison0578
#print axioms sourceMap0578_checked
#print axioms fusedMap0578_checked
#print axioms certified0578
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
