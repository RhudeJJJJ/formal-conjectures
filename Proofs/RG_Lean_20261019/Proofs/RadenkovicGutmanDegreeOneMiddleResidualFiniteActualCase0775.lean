/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0775 : Family 10 := level10.get ⟨432,by decide⟩
def sourceMap0775 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0775 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0775_checked : acceptsGraphIso
    (source (graph core0775) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1886.graph sourceMap0775=true := by decide +kernel
theorem fusedMap0775_checked : acceptsGraphIso
    (fused (graph core0775) (root 10) 2 2) DegreeTwoThreeSpectrum5836.graph fusedMap0775=true := by decide +kernel
theorem certified0775 : Certified (graph core0775) (root 10) 2 2 :=
  of_native_maps core0775 DegreeOneMiddleResidualSpectrum1886.graph DegreeTwoThreeSpectrum5836.graph
    sourceMap0775 fusedMap0775 sourceMap0775_checked fusedMap0775_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0775
#print axioms sourceMap0775_checked
#print axioms fusedMap0775_checked
#print axioms certified0775
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
