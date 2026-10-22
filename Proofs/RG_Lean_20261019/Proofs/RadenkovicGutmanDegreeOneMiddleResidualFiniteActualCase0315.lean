/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0315 : Family 9 := level9.get ⟨167,by decide⟩
def sourceMap0315 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap0315 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0315_checked : acceptsGraphIso
    (source (graph core0315) (root 9) 2 2) DegreeOneMiddleResidualSpectrum793.graph sourceMap0315=true := by decide +kernel
theorem fusedMap0315_checked : acceptsGraphIso
    (fused (graph core0315) (root 9) 2 2) DegreeTwoThreeSpectrum3929.graph fusedMap0315=true := by decide +kernel
theorem certified0315 : Certified (graph core0315) (root 9) 2 2 :=
  of_native_maps core0315 DegreeOneMiddleResidualSpectrum793.graph DegreeTwoThreeSpectrum3929.graph
    sourceMap0315 fusedMap0315 sourceMap0315_checked fusedMap0315_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0315
#print axioms sourceMap0315_checked
#print axioms fusedMap0315_checked
#print axioms certified0315
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
