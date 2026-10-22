/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0558 : Family 10 := level10.get ⟨574,by decide⟩
def sourceMap0558 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0558 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap0558_checked : acceptsGraphIso
    (source (graph core0558) (root 10) 0 0) DegreeOneSmallSpectrum1657.graph sourceMap0558=true := by decide +kernel
theorem fusedMap0558_checked : acceptsGraphIso
    (fused (graph core0558) (root 10) 0 0) DegreeOneSmallSpectrum1107.graph fusedMap0558=true := by decide +kernel
theorem certified0558 : Certified (graph core0558) (root 10) 0 0 :=
  of_native_maps core0558 DegreeOneSmallSpectrum1657.graph DegreeOneSmallSpectrum1107.graph
    sourceMap0558 fusedMap0558 sourceMap0558_checked fusedMap0558_checked
    DegreeTwoThreeFiniteComparisons.comparison0558
#print axioms sourceMap0558_checked
#print axioms fusedMap0558_checked
#print axioms certified0558
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
