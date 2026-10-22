/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0576 : Family 10 := level10.get ⟨115,by decide⟩
def sourceMap0576 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0576 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0576_checked : acceptsGraphIso
    (source (graph core0576) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1828.graph sourceMap0576=true := by decide +kernel
theorem fusedMap0576_checked : acceptsGraphIso
    (fused (graph core0576) (root 10) 2 2) DegreeTwoThreeSpectrum5040.graph fusedMap0576=true := by decide +kernel
theorem certified0576 : Certified (graph core0576) (root 10) 2 2 :=
  of_native_maps core0576 DegreeOneMiddleResidualSpectrum1828.graph DegreeTwoThreeSpectrum5040.graph
    sourceMap0576 fusedMap0576 sourceMap0576_checked fusedMap0576_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0576
#print axioms sourceMap0576_checked
#print axioms fusedMap0576_checked
#print axioms certified0576
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
