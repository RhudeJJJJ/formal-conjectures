/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0225 : Family 9 := level9.get ⟨31,by decide⟩
def sourceMap0225 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![2,1,0,9,10,11,12,13,14,15,3,4,5,6,7,8] (sourceLabel 9 2 2 v)
def fusedMap0225 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0225_checked : acceptsGraphIso
    (source (graph core0225) (root 9) 2 2) DegreeOneMiddleResidualSpectrum726.graph sourceMap0225=true := by decide +kernel
theorem fusedMap0225_checked : acceptsGraphIso
    (fused (graph core0225) (root 9) 2 2) DegreeTwoThreeSpectrum3879.graph fusedMap0225=true := by decide +kernel
theorem certified0225 : Certified (graph core0225) (root 9) 2 2 :=
  of_native_maps core0225 DegreeOneMiddleResidualSpectrum726.graph DegreeTwoThreeSpectrum3879.graph
    sourceMap0225 fusedMap0225 sourceMap0225_checked fusedMap0225_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0225
#print axioms sourceMap0225_checked
#print axioms fusedMap0225_checked
#print axioms certified0225
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
