/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0220 : Family 9 := level9.get ⟨25,by decide⟩
def sourceMap0220 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![2,1,0,9,10,11,12,13,14,15,3,4,5,6,7,8] (sourceLabel 9 2 2 v)
def fusedMap0220 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0220_checked : acceptsGraphIso
    (source (graph core0220) (root 9) 2 2) DegreeOneMiddleResidualSpectrum718.graph sourceMap0220=true := by decide +kernel
theorem fusedMap0220_checked : acceptsGraphIso
    (fused (graph core0220) (root 9) 2 2) DegreeTwoThreeSpectrum3872.graph fusedMap0220=true := by decide +kernel
theorem certified0220 : Certified (graph core0220) (root 9) 2 2 :=
  of_native_maps core0220 DegreeOneMiddleResidualSpectrum718.graph DegreeTwoThreeSpectrum3872.graph
    sourceMap0220 fusedMap0220 sourceMap0220_checked fusedMap0220_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0220
#print axioms sourceMap0220_checked
#print axioms fusedMap0220_checked
#print axioms certified0220
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
