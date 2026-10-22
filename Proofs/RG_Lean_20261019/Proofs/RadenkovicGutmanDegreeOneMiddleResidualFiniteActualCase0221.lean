/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0221 : Family 9 := level9.get ⟨26,by decide⟩
def sourceMap0221 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![2,1,0,9,10,11,12,13,14,15,3,4,5,6,7,8] (sourceLabel 9 2 2 v)
def fusedMap0221 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0221_checked : acceptsGraphIso
    (source (graph core0221) (root 9) 2 2) DegreeOneMiddleResidualSpectrum719.graph sourceMap0221=true := by decide +kernel
theorem fusedMap0221_checked : acceptsGraphIso
    (fused (graph core0221) (root 9) 2 2) DegreeTwoThreeSpectrum3873.graph fusedMap0221=true := by decide +kernel
theorem certified0221 : Certified (graph core0221) (root 9) 2 2 :=
  of_native_maps core0221 DegreeOneMiddleResidualSpectrum719.graph DegreeTwoThreeSpectrum3873.graph
    sourceMap0221 fusedMap0221 sourceMap0221_checked fusedMap0221_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0221
#print axioms sourceMap0221_checked
#print axioms fusedMap0221_checked
#print axioms certified0221
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
