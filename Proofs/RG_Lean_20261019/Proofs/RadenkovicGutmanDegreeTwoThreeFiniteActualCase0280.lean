/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0280 : Family 9 := level9.get ⟨389,by decide⟩
def sourceMap0280 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0280 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,9,10,11,8,6,7] (fusedLabel 9 0 0 v)
theorem sourceMap0280_checked : acceptsGraphIso
    (source (graph core0280) (root 9) 0 0) DegreeOneSmallSpectrum766.graph sourceMap0280=true := by decide +kernel
theorem fusedMap0280_checked : acceptsGraphIso
    (fused (graph core0280) (root 9) 0 0) DegreeOneSmallSpectrum761.graph fusedMap0280=true := by decide +kernel
theorem certified0280 : Certified (graph core0280) (root 9) 0 0 :=
  of_native_maps core0280 DegreeOneSmallSpectrum766.graph DegreeOneSmallSpectrum761.graph
    sourceMap0280 fusedMap0280 sourceMap0280_checked fusedMap0280_checked
    DegreeTwoThreeFiniteComparisons.comparison0280
#print axioms sourceMap0280_checked
#print axioms fusedMap0280_checked
#print axioms certified0280
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
