/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0538 : Family 10 := level10.get ⟨65,by decide⟩
def sourceMap0538 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0538 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0538_checked : acceptsGraphIso
    (source (graph core0538) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1653.graph sourceMap0538=true := by decide +kernel
theorem fusedMap0538_checked : acceptsGraphIso
    (fused (graph core0538) (root 10) 2 2) DegreeTwoThreeSpectrum4978.graph fusedMap0538=true := by decide +kernel
theorem certified0538 : Certified (graph core0538) (root 10) 2 2 :=
  of_native_maps core0538 DegreeOneMiddleResidualSpectrum1653.graph DegreeTwoThreeSpectrum4978.graph
    sourceMap0538 fusedMap0538 sourceMap0538_checked fusedMap0538_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0538
#print axioms sourceMap0538_checked
#print axioms fusedMap0538_checked
#print axioms certified0538
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
