/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0945 : Family 10 := level10.get ⟨767,by decide⟩
def sourceMap0945 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0945 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0945_checked : acceptsGraphIso
    (source (graph core0945) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2228.graph sourceMap0945=true := by decide +kernel
theorem fusedMap0945_checked : acceptsGraphIso
    (fused (graph core0945) (root 10) 2 2) DegreeTwoThreeSpectrum5545.graph fusedMap0945=true := by decide +kernel
theorem certified0945 : Certified (graph core0945) (root 10) 2 2 :=
  of_native_maps core0945 DegreeOneMiddleResidualSpectrum2228.graph DegreeTwoThreeSpectrum5545.graph
    sourceMap0945 fusedMap0945 sourceMap0945_checked fusedMap0945_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0945
#print axioms sourceMap0945_checked
#print axioms fusedMap0945_checked
#print axioms certified0945
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
