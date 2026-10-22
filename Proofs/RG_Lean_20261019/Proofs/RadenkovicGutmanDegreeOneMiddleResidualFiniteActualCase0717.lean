/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0717 : Family 10 := level10.get ⟨331,by decide⟩
def sourceMap0717 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0717 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0717_checked : acceptsGraphIso
    (source (graph core0717) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1801.graph sourceMap0717=true := by decide +kernel
theorem fusedMap0717_checked : acceptsGraphIso
    (fused (graph core0717) (root 10) 2 2) DegreeTwoThreeSpectrum5570.graph fusedMap0717=true := by decide +kernel
theorem certified0717 : Certified (graph core0717) (root 10) 2 2 :=
  of_native_maps core0717 DegreeOneMiddleResidualSpectrum1801.graph DegreeTwoThreeSpectrum5570.graph
    sourceMap0717 fusedMap0717 sourceMap0717_checked fusedMap0717_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0717
#print axioms sourceMap0717_checked
#print axioms fusedMap0717_checked
#print axioms certified0717
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
