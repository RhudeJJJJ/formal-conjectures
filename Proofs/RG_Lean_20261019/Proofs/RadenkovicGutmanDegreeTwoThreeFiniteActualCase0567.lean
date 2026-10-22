/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0567 : Family 10 := level10.get ⟨601,by decide⟩
def sourceMap0567 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0567 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0567_checked : acceptsGraphIso
    (source (graph core0567) (root 10) 0 0) DegreeOneSmallSpectrum1152.graph sourceMap0567=true := by decide +kernel
theorem fusedMap0567_checked : acceptsGraphIso
    (fused (graph core0567) (root 10) 0 0) DegreeOneSmallSpectrum1151.graph fusedMap0567=true := by decide +kernel
theorem certified0567 : Certified (graph core0567) (root 10) 0 0 :=
  of_native_maps core0567 DegreeOneSmallSpectrum1152.graph DegreeOneSmallSpectrum1151.graph
    sourceMap0567 fusedMap0567 sourceMap0567_checked fusedMap0567_checked
    DegreeTwoThreeFiniteComparisons.comparison0567
#print axioms sourceMap0567_checked
#print axioms fusedMap0567_checked
#print axioms certified0567
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
