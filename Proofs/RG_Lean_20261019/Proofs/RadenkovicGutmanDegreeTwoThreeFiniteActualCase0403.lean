/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0403 : Family 10 := level10.get ⟨38,by decide⟩
def sourceMap0403 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0403 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,6,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap0403_checked : acceptsGraphIso
    (source (graph core0403) (root 10) 0 0) DegreeOneSmallSpectrum869.graph sourceMap0403=true := by decide +kernel
theorem fusedMap0403_checked : acceptsGraphIso
    (fused (graph core0403) (root 10) 0 0) DegreeOneSmallSpectrum943.graph fusedMap0403=true := by decide +kernel
theorem certified0403 : Certified (graph core0403) (root 10) 0 0 :=
  of_native_maps core0403 DegreeOneSmallSpectrum869.graph DegreeOneSmallSpectrum943.graph
    sourceMap0403 fusedMap0403 sourceMap0403_checked fusedMap0403_checked
    DegreeTwoThreeFiniteComparisons.comparison0403
#print axioms sourceMap0403_checked
#print axioms fusedMap0403_checked
#print axioms certified0403
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
