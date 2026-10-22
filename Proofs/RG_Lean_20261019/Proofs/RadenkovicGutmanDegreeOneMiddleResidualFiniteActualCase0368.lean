/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0368 : Family 9 := level9.get ⟨263,by decide⟩
def sourceMap0368 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0368 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0368_checked : acceptsGraphIso
    (source (graph core0368) (root 9) 2 2) DegreeOneMiddleResidualSpectrum887.graph sourceMap0368=true := by decide +kernel
theorem fusedMap0368_checked : acceptsGraphIso
    (fused (graph core0368) (root 9) 2 2) DegreeTwoThreeSpectrum4073.graph fusedMap0368=true := by decide +kernel
theorem certified0368 : Certified (graph core0368) (root 9) 2 2 :=
  of_native_maps core0368 DegreeOneMiddleResidualSpectrum887.graph DegreeTwoThreeSpectrum4073.graph
    sourceMap0368 fusedMap0368 sourceMap0368_checked fusedMap0368_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0368
#print axioms sourceMap0368_checked
#print axioms fusedMap0368_checked
#print axioms certified0368
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
