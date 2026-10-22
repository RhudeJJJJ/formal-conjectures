/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0637 : Family 10 := level10.get ⟨208,by decide⟩
def sourceMap0637 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0637 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0637_checked : acceptsGraphIso
    (source (graph core0637) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1587.graph sourceMap0637=true := by decide +kernel
theorem fusedMap0637_checked : acceptsGraphIso
    (fused (graph core0637) (root 10) 2 2) DegreeTwoThreeSpectrum5210.graph fusedMap0637=true := by decide +kernel
theorem certified0637 : Certified (graph core0637) (root 10) 2 2 :=
  of_native_maps core0637 DegreeOneMiddleResidualSpectrum1587.graph DegreeTwoThreeSpectrum5210.graph
    sourceMap0637 fusedMap0637 sourceMap0637_checked fusedMap0637_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0637
#print axioms sourceMap0637_checked
#print axioms fusedMap0637_checked
#print axioms certified0637
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
