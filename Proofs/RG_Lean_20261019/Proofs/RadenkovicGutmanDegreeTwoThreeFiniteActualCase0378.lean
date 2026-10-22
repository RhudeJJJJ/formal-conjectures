/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0378 : Family 9 := level9.get ⟨622,by decide⟩
def sourceMap0378 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,8,9,10,11,1,2,3,4,5,6,7] (sourceLabel 9 0 0 v)
def fusedMap0378 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,8,9,10,11,1,2,3,4,5,6,7] (fusedLabel 9 0 0 v)
theorem sourceMap0378_checked : acceptsGraphIso
    (source (graph core0378) (root 9) 0 0) DegreeOneSmallSpectrum610.graph sourceMap0378=true := by decide +kernel
theorem fusedMap0378_checked : acceptsGraphIso
    (fused (graph core0378) (root 9) 0 0) DegreeOneSmallSpectrum606.graph fusedMap0378=true := by decide +kernel
theorem certified0378 : Certified (graph core0378) (root 9) 0 0 :=
  of_native_maps core0378 DegreeOneSmallSpectrum610.graph DegreeOneSmallSpectrum606.graph
    sourceMap0378 fusedMap0378 sourceMap0378_checked fusedMap0378_checked
    DegreeTwoThreeFiniteComparisons.comparison0378
#print axioms sourceMap0378_checked
#print axioms fusedMap0378_checked
#print axioms certified0378
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
