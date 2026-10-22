/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0765 : Family 10 := level10.get ⟨411,by decide⟩
def sourceMap0765 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,8,9,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0765 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0765_checked : acceptsGraphIso
    (source (graph core0765) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1856.graph sourceMap0765=true := by decide +kernel
theorem fusedMap0765_checked : acceptsGraphIso
    (fused (graph core0765) (root 10) 2 2) DegreeTwoThreeSpectrum5786.graph fusedMap0765=true := by decide +kernel
theorem certified0765 : Certified (graph core0765) (root 10) 2 2 :=
  of_native_maps core0765 DegreeOneMiddleResidualSpectrum1856.graph DegreeTwoThreeSpectrum5786.graph
    sourceMap0765 fusedMap0765 sourceMap0765_checked fusedMap0765_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0765
#print axioms sourceMap0765_checked
#print axioms fusedMap0765_checked
#print axioms certified0765
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
