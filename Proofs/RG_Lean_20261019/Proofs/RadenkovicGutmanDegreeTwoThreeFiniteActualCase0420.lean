/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0420 : Family 10 := level10.get ⟨116,by decide⟩
def sourceMap0420 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,7,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0420 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0420_checked : acceptsGraphIso
    (source (graph core0420) (root 10) 0 0) DegreeOneSmallSpectrum1033.graph sourceMap0420=true := by decide +kernel
theorem fusedMap0420_checked : acceptsGraphIso
    (fused (graph core0420) (root 10) 0 0) DegreeOneSmallSpectrum926.graph fusedMap0420=true := by decide +kernel
theorem certified0420 : Certified (graph core0420) (root 10) 0 0 :=
  of_native_maps core0420 DegreeOneSmallSpectrum1033.graph DegreeOneSmallSpectrum926.graph
    sourceMap0420 fusedMap0420 sourceMap0420_checked fusedMap0420_checked
    DegreeTwoThreeFiniteComparisons.comparison0420
#print axioms sourceMap0420_checked
#print axioms fusedMap0420_checked
#print axioms certified0420
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
