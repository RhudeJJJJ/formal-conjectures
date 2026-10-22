/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0323 : Family 9 := level9.get ⟨180,by decide⟩
def sourceMap0323 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap0323 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0323_checked : acceptsGraphIso
    (source (graph core0323) (root 9) 2 2) DegreeOneMiddleResidualSpectrum809.graph sourceMap0323=true := by decide +kernel
theorem fusedMap0323_checked : acceptsGraphIso
    (fused (graph core0323) (root 9) 2 2) DegreeTwoThreeSpectrum3947.graph fusedMap0323=true := by decide +kernel
theorem certified0323 : Certified (graph core0323) (root 9) 2 2 :=
  of_native_maps core0323 DegreeOneMiddleResidualSpectrum809.graph DegreeTwoThreeSpectrum3947.graph
    sourceMap0323 fusedMap0323 sourceMap0323_checked fusedMap0323_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0323
#print axioms sourceMap0323_checked
#print axioms fusedMap0323_checked
#print axioms certified0323
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
