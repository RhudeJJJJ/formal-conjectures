/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0147 : Family 8 := level8.get ⟨144,by decide⟩
def sourceMap0147 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0147 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0147_checked : acceptsGraphIso
    (source (graph core0147) (root 8) 2 2) DegreeOneMiddleResidualSpectrum311.graph sourceMap0147=true := by decide +kernel
theorem fusedMap0147_checked : acceptsGraphIso
    (fused (graph core0147) (root 8) 2 2) DegreeTwoThreeSpectrum2706.graph fusedMap0147=true := by decide +kernel
theorem certified0147 : Certified (graph core0147) (root 8) 2 2 :=
  of_native_maps core0147 DegreeOneMiddleResidualSpectrum311.graph DegreeTwoThreeSpectrum2706.graph
    sourceMap0147 fusedMap0147 sourceMap0147_checked fusedMap0147_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0147
#print axioms sourceMap0147_checked
#print axioms fusedMap0147_checked
#print axioms certified0147
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
