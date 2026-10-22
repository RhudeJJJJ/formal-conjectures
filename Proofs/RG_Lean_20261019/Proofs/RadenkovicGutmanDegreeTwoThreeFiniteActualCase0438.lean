/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0438 : Family 10 := level10.get ⟨182,by decide⟩
def sourceMap0438 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,9,10,11,12,7,8,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0438 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0438_checked : acceptsGraphIso
    (source (graph core0438) (root 10) 0 0) DegreeOneSmallSpectrum1021.graph sourceMap0438=true := by decide +kernel
theorem fusedMap0438_checked : acceptsGraphIso
    (fused (graph core0438) (root 10) 0 0) DegreeOneSmallSpectrum924.graph fusedMap0438=true := by decide +kernel
theorem certified0438 : Certified (graph core0438) (root 10) 0 0 :=
  of_native_maps core0438 DegreeOneSmallSpectrum1021.graph DegreeOneSmallSpectrum924.graph
    sourceMap0438 fusedMap0438 sourceMap0438_checked fusedMap0438_checked
    DegreeTwoThreeFiniteComparisons.comparison0438
#print axioms sourceMap0438_checked
#print axioms fusedMap0438_checked
#print axioms certified0438
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
