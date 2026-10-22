/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0042 : Family 7 := level7.get ⟨71,by decide⟩
def sourceMap0042 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 7 2 2 v)
def fusedMap0042 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0042_checked : acceptsGraphIso
    (source (graph core0042) (root 7) 2 2) DegreeOneMiddleResidualSpectrum099.graph sourceMap0042=true := by decide +kernel
theorem fusedMap0042_checked : acceptsGraphIso
    (fused (graph core0042) (root 7) 2 2) DegreeTwoThreeSpectrum1758.graph fusedMap0042=true := by decide +kernel
theorem certified0042 : Certified (graph core0042) (root 7) 2 2 :=
  of_native_maps core0042 DegreeOneMiddleResidualSpectrum099.graph DegreeTwoThreeSpectrum1758.graph
    sourceMap0042 fusedMap0042 sourceMap0042_checked fusedMap0042_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0042
#print axioms sourceMap0042_checked
#print axioms fusedMap0042_checked
#print axioms certified0042
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
