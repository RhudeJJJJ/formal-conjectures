/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0430 : Family 10 := level10.get ⟨158,by decide⟩
def sourceMap0430 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,7,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0430 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0430_checked : acceptsGraphIso
    (source (graph core0430) (root 10) 0 0) DegreeOneSmallSpectrum1059.graph sourceMap0430=true := by decide +kernel
theorem fusedMap0430_checked : acceptsGraphIso
    (fused (graph core0430) (root 10) 0 0) DegreeOneSmallSpectrum934.graph fusedMap0430=true := by decide +kernel
theorem certified0430 : Certified (graph core0430) (root 10) 0 0 :=
  of_native_maps core0430 DegreeOneSmallSpectrum1059.graph DegreeOneSmallSpectrum934.graph
    sourceMap0430 fusedMap0430 sourceMap0430_checked fusedMap0430_checked
    DegreeTwoThreeFiniteComparisons.comparison0430
#print axioms sourceMap0430_checked
#print axioms fusedMap0430_checked
#print axioms certified0430
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
