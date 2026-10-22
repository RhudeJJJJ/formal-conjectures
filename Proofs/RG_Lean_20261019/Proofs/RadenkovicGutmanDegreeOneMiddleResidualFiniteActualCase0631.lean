/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0631 : Family 10 := level10.get ⟨201,by decide⟩
def sourceMap0631 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0631 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0631_checked : acceptsGraphIso
    (source (graph core0631) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1579.graph sourceMap0631=true := by decide +kernel
theorem fusedMap0631_checked : acceptsGraphIso
    (fused (graph core0631) (root 10) 2 2) DegreeTwoThreeSpectrum5188.graph fusedMap0631=true := by decide +kernel
theorem certified0631 : Certified (graph core0631) (root 10) 2 2 :=
  of_native_maps core0631 DegreeOneMiddleResidualSpectrum1579.graph DegreeTwoThreeSpectrum5188.graph
    sourceMap0631 fusedMap0631 sourceMap0631_checked fusedMap0631_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0631
#print axioms sourceMap0631_checked
#print axioms fusedMap0631_checked
#print axioms certified0631
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
