/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0260 : Family 9 := level9.get ⟨80,by decide⟩
def sourceMap0260 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0260 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0260_checked : acceptsGraphIso
    (source (graph core0260) (root 9) 2 2) DegreeOneMiddleResidualSpectrum676.graph sourceMap0260=true := by decide +kernel
theorem fusedMap0260_checked : acceptsGraphIso
    (fused (graph core0260) (root 9) 2 2) DegreeTwoThreeSpectrum4026.graph fusedMap0260=true := by decide +kernel
theorem certified0260 : Certified (graph core0260) (root 9) 2 2 :=
  of_native_maps core0260 DegreeOneMiddleResidualSpectrum676.graph DegreeTwoThreeSpectrum4026.graph
    sourceMap0260 fusedMap0260 sourceMap0260_checked fusedMap0260_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0260
#print axioms sourceMap0260_checked
#print axioms fusedMap0260_checked
#print axioms certified0260
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
