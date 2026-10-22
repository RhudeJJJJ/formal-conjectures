/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0776 : Family 10 := level10.get ⟨434,by decide⟩
def sourceMap0776 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0776 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0776_checked : acceptsGraphIso
    (source (graph core0776) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1929.graph sourceMap0776=true := by decide +kernel
theorem fusedMap0776_checked : acceptsGraphIso
    (fused (graph core0776) (root 10) 2 2) DegreeTwoThreeSpectrum5842.graph fusedMap0776=true := by decide +kernel
theorem certified0776 : Certified (graph core0776) (root 10) 2 2 :=
  of_native_maps core0776 DegreeOneMiddleResidualSpectrum1929.graph DegreeTwoThreeSpectrum5842.graph
    sourceMap0776 fusedMap0776 sourceMap0776_checked fusedMap0776_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0776
#print axioms sourceMap0776_checked
#print axioms fusedMap0776_checked
#print axioms certified0776
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
