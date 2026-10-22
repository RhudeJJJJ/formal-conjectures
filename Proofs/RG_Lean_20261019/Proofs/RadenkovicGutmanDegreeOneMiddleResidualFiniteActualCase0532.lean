/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0532 : Family 10 := level10.get ⟨58,by decide⟩
def sourceMap0532 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0532 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0532_checked : acceptsGraphIso
    (source (graph core0532) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1591.graph sourceMap0532=true := by decide +kernel
theorem fusedMap0532_checked : acceptsGraphIso
    (fused (graph core0532) (root 10) 2 2) DegreeTwoThreeSpectrum4970.graph fusedMap0532=true := by decide +kernel
theorem certified0532 : Certified (graph core0532) (root 10) 2 2 :=
  of_native_maps core0532 DegreeOneMiddleResidualSpectrum1591.graph DegreeTwoThreeSpectrum4970.graph
    sourceMap0532 fusedMap0532 sourceMap0532_checked fusedMap0532_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0532
#print axioms sourceMap0532_checked
#print axioms fusedMap0532_checked
#print axioms certified0532
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
