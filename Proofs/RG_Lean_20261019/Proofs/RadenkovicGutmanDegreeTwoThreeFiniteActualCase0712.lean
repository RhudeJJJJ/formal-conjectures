/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0712 : Family 10 := level10.get ⟨981,by decide⟩
def sourceMap0712 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,2,3,4,5,6,7,8] (sourceLabel 10 0 0 v)
def fusedMap0712 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,2,3,4,5,6,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap0712_checked : acceptsGraphIso
    (source (graph core0712) (root 10) 0 0) DegreeOneSmallSpectrum1147.graph sourceMap0712=true := by decide +kernel
theorem fusedMap0712_checked : acceptsGraphIso
    (fused (graph core0712) (root 10) 0 0) DegreeOneSmallSpectrum1142.graph fusedMap0712=true := by decide +kernel
theorem certified0712 : Certified (graph core0712) (root 10) 0 0 :=
  of_native_maps core0712 DegreeOneSmallSpectrum1147.graph DegreeOneSmallSpectrum1142.graph
    sourceMap0712 fusedMap0712 sourceMap0712_checked fusedMap0712_checked
    DegreeTwoThreeFiniteComparisons.comparison0712
#print axioms sourceMap0712_checked
#print axioms fusedMap0712_checked
#print axioms certified0712
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
