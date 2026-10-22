/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0142 : Family 8 := level8.get ⟨134,by decide⟩
def sourceMap0142 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0142 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0142_checked : acceptsGraphIso
    (source (graph core0142) (root 8) 2 2) DegreeOneMiddleResidualSpectrum301.graph sourceMap0142=true := by decide +kernel
theorem fusedMap0142_checked : acceptsGraphIso
    (fused (graph core0142) (root 8) 2 2) DegreeTwoThreeSpectrum2654.graph fusedMap0142=true := by decide +kernel
theorem certified0142 : Certified (graph core0142) (root 8) 2 2 :=
  of_native_maps core0142 DegreeOneMiddleResidualSpectrum301.graph DegreeTwoThreeSpectrum2654.graph
    sourceMap0142 fusedMap0142 sourceMap0142_checked fusedMap0142_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0142
#print axioms sourceMap0142_checked
#print axioms fusedMap0142_checked
#print axioms certified0142
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
