/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0721 : Family 10 := level10.get ⟨337,by decide⟩
def sourceMap0721 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0721 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0721_checked : acceptsGraphIso
    (source (graph core0721) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1807.graph sourceMap0721=true := by decide +kernel
theorem fusedMap0721_checked : acceptsGraphIso
    (fused (graph core0721) (root 10) 2 2) DegreeTwoThreeSpectrum5588.graph fusedMap0721=true := by decide +kernel
theorem certified0721 : Certified (graph core0721) (root 10) 2 2 :=
  of_native_maps core0721 DegreeOneMiddleResidualSpectrum1807.graph DegreeTwoThreeSpectrum5588.graph
    sourceMap0721 fusedMap0721 sourceMap0721_checked fusedMap0721_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0721
#print axioms sourceMap0721_checked
#print axioms fusedMap0721_checked
#print axioms certified0721
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
