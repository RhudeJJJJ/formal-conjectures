/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0498 : Family 10 := level10.get ⟨15,by decide⟩
def sourceMap0498 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0498 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0498_checked : acceptsGraphIso
    (source (graph core0498) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1230.graph sourceMap0498=true := by decide +kernel
theorem fusedMap0498_checked : acceptsGraphIso
    (fused (graph core0498) (root 10) 2 2) DegreeTwoThreeSpectrum5002.graph fusedMap0498=true := by decide +kernel
theorem certified0498 : Certified (graph core0498) (root 10) 2 2 :=
  of_native_maps core0498 DegreeOneMiddleResidualSpectrum1230.graph DegreeTwoThreeSpectrum5002.graph
    sourceMap0498 fusedMap0498 sourceMap0498_checked fusedMap0498_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0498
#print axioms sourceMap0498_checked
#print axioms fusedMap0498_checked
#print axioms certified0498
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
