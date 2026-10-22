/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0236 : Family 9 := level9.get ⟨47,by decide⟩
def sourceMap0236 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap0236 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0236_checked : acceptsGraphIso
    (source (graph core0236) (root 9) 2 2) DegreeOneMiddleResidualSpectrum587.graph sourceMap0236=true := by decide +kernel
theorem fusedMap0236_checked : acceptsGraphIso
    (fused (graph core0236) (root 9) 2 2) DegreeTwoThreeSpectrum3914.graph fusedMap0236=true := by decide +kernel
theorem certified0236 : Certified (graph core0236) (root 9) 2 2 :=
  of_native_maps core0236 DegreeOneMiddleResidualSpectrum587.graph DegreeTwoThreeSpectrum3914.graph
    sourceMap0236 fusedMap0236 sourceMap0236_checked fusedMap0236_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0236
#print axioms sourceMap0236_checked
#print axioms fusedMap0236_checked
#print axioms certified0236
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
