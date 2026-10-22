/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0536 : Family 10 := level10.get ⟨63,by decide⟩
def sourceMap0536 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0536 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0536_checked : acceptsGraphIso
    (source (graph core0536) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1650.graph sourceMap0536=true := by decide +kernel
theorem fusedMap0536_checked : acceptsGraphIso
    (fused (graph core0536) (root 10) 2 2) DegreeTwoThreeSpectrum4976.graph fusedMap0536=true := by decide +kernel
theorem certified0536 : Certified (graph core0536) (root 10) 2 2 :=
  of_native_maps core0536 DegreeOneMiddleResidualSpectrum1650.graph DegreeTwoThreeSpectrum4976.graph
    sourceMap0536 fusedMap0536 sourceMap0536_checked fusedMap0536_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0536
#print axioms sourceMap0536_checked
#print axioms fusedMap0536_checked
#print axioms certified0536
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
