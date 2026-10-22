/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0014 : Family 7 := level7.get ⟨17,by decide⟩
def sourceMap0014 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,8,9,10,11,12,13,2,3,4,5,6,7] (sourceLabel 7 2 2 v)
def fusedMap0014 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0014_checked : acceptsGraphIso
    (source (graph core0014) (root 7) 2 2) DegreeOneMiddleResidualSpectrum087.graph sourceMap0014=true := by decide +kernel
theorem fusedMap0014_checked : acceptsGraphIso
    (fused (graph core0014) (root 7) 2 2) DegreeTwoThreeSpectrum1723.graph fusedMap0014=true := by decide +kernel
theorem certified0014 : Certified (graph core0014) (root 7) 2 2 :=
  of_native_maps core0014 DegreeOneMiddleResidualSpectrum087.graph DegreeTwoThreeSpectrum1723.graph
    sourceMap0014 fusedMap0014 sourceMap0014_checked fusedMap0014_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0014
#print axioms sourceMap0014_checked
#print axioms fusedMap0014_checked
#print axioms certified0014
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
