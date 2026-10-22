/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0130 : Family 8 := level8.get ⟨109,by decide⟩
def sourceMap0130 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0130 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0130_checked : acceptsGraphIso
    (source (graph core0130) (root 8) 2 2) DegreeOneMiddleResidualSpectrum277.graph sourceMap0130=true := by decide +kernel
theorem fusedMap0130_checked : acceptsGraphIso
    (fused (graph core0130) (root 8) 2 2) DegreeTwoThreeSpectrum2509.graph fusedMap0130=true := by decide +kernel
theorem certified0130 : Certified (graph core0130) (root 8) 2 2 :=
  of_native_maps core0130 DegreeOneMiddleResidualSpectrum277.graph DegreeTwoThreeSpectrum2509.graph
    sourceMap0130 fusedMap0130 sourceMap0130_checked fusedMap0130_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0130
#print axioms sourceMap0130_checked
#print axioms fusedMap0130_checked
#print axioms certified0130
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
