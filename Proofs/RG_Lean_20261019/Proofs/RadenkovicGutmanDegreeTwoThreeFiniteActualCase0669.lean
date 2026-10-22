/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0669 : Family 10 := level10.get ⟨886,by decide⟩
def sourceMap0669 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0669 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,6,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0669_checked : acceptsGraphIso
    (source (graph core0669) (root 10) 0 0) DegreeOneSmallSpectrum1637.graph sourceMap0669=true := by decide +kernel
theorem fusedMap0669_checked : acceptsGraphIso
    (fused (graph core0669) (root 10) 0 0) DegreeOneSmallSpectrum1412.graph fusedMap0669=true := by decide +kernel
theorem certified0669 : Certified (graph core0669) (root 10) 0 0 :=
  of_native_maps core0669 DegreeOneSmallSpectrum1637.graph DegreeOneSmallSpectrum1412.graph
    sourceMap0669 fusedMap0669 sourceMap0669_checked fusedMap0669_checked
    DegreeTwoThreeFiniteComparisons.comparison0669
#print axioms sourceMap0669_checked
#print axioms fusedMap0669_checked
#print axioms certified0669
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
