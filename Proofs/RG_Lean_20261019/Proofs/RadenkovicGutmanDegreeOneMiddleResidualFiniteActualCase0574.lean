/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0574 : Family 10 := level10.get ⟨112,by decide⟩
def sourceMap0574 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,7,0,1,2,3,4,5,6,16,15,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0574 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0574_checked : acceptsGraphIso
    (source (graph core0574) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1829.graph sourceMap0574=true := by decide +kernel
theorem fusedMap0574_checked : acceptsGraphIso
    (fused (graph core0574) (root 10) 2 2) DegreeTwoThreeSpectrum5036.graph fusedMap0574=true := by decide +kernel
theorem certified0574 : Certified (graph core0574) (root 10) 2 2 :=
  of_native_maps core0574 DegreeOneMiddleResidualSpectrum1829.graph DegreeTwoThreeSpectrum5036.graph
    sourceMap0574 fusedMap0574 sourceMap0574_checked fusedMap0574_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0574
#print axioms sourceMap0574_checked
#print axioms fusedMap0574_checked
#print axioms certified0574
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
