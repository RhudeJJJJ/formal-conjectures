/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0136 : Family 8 := level8.get ⟨120,by decide⟩
def sourceMap0136 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0136 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0136_checked : acceptsGraphIso
    (source (graph core0136) (root 8) 2 2) DegreeOneMiddleResidualSpectrum289.graph sourceMap0136=true := by decide +kernel
theorem fusedMap0136_checked : acceptsGraphIso
    (fused (graph core0136) (root 8) 2 2) DegreeTwoThreeSpectrum2565.graph fusedMap0136=true := by decide +kernel
theorem certified0136 : Certified (graph core0136) (root 8) 2 2 :=
  of_native_maps core0136 DegreeOneMiddleResidualSpectrum289.graph DegreeTwoThreeSpectrum2565.graph
    sourceMap0136 fusedMap0136 sourceMap0136_checked fusedMap0136_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0136
#print axioms sourceMap0136_checked
#print axioms fusedMap0136_checked
#print axioms certified0136
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
