/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0572 : Family 10 := level10.get ⟨110,by decide⟩
def sourceMap0572 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0572 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0572_checked : acceptsGraphIso
    (source (graph core0572) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1830.graph sourceMap0572=true := by decide +kernel
theorem fusedMap0572_checked : acceptsGraphIso
    (fused (graph core0572) (root 10) 2 2) DegreeTwoThreeSpectrum5034.graph fusedMap0572=true := by decide +kernel
theorem certified0572 : Certified (graph core0572) (root 10) 2 2 :=
  of_native_maps core0572 DegreeOneMiddleResidualSpectrum1830.graph DegreeTwoThreeSpectrum5034.graph
    sourceMap0572 fusedMap0572 sourceMap0572_checked fusedMap0572_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0572
#print axioms sourceMap0572_checked
#print axioms fusedMap0572_checked
#print axioms certified0572
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
