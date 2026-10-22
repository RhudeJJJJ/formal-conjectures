/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0571 : Family 10 := level10.get ⟨108,by decide⟩
def sourceMap0571 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0571 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0571_checked : acceptsGraphIso
    (source (graph core0571) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1821.graph sourceMap0571=true := by decide +kernel
theorem fusedMap0571_checked : acceptsGraphIso
    (fused (graph core0571) (root 10) 2 2) DegreeTwoThreeSpectrum5031.graph fusedMap0571=true := by decide +kernel
theorem certified0571 : Certified (graph core0571) (root 10) 2 2 :=
  of_native_maps core0571 DegreeOneMiddleResidualSpectrum1821.graph DegreeTwoThreeSpectrum5031.graph
    sourceMap0571 fusedMap0571 sourceMap0571_checked fusedMap0571_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0571
#print axioms sourceMap0571_checked
#print axioms fusedMap0571_checked
#print axioms certified0571
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
