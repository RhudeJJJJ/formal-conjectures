/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0579 : Family 10 := level10.get ⟨638,by decide⟩
def sourceMap0579 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0579 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap0579_checked : acceptsGraphIso
    (source (graph core0579) (root 10) 0 0) DegreeOneSmallSpectrum1662.graph sourceMap0579=true := by decide +kernel
theorem fusedMap0579_checked : acceptsGraphIso
    (fused (graph core0579) (root 10) 0 0) DegreeOneSmallSpectrum1221.graph fusedMap0579=true := by decide +kernel
theorem certified0579 : Certified (graph core0579) (root 10) 0 0 :=
  of_native_maps core0579 DegreeOneSmallSpectrum1662.graph DegreeOneSmallSpectrum1221.graph
    sourceMap0579 fusedMap0579 sourceMap0579_checked fusedMap0579_checked
    DegreeTwoThreeFiniteComparisons.comparison0579
#print axioms sourceMap0579_checked
#print axioms fusedMap0579_checked
#print axioms certified0579
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
