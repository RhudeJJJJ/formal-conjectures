/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0738 : Family 10 := level10.get ⟨371,by decide⟩
def sourceMap0738 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0738 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0738_checked : acceptsGraphIso
    (source (graph core0738) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1896.graph sourceMap0738=true := by decide +kernel
theorem fusedMap0738_checked : acceptsGraphIso
    (fused (graph core0738) (root 10) 2 2) DegreeTwoThreeSpectrum5675.graph fusedMap0738=true := by decide +kernel
theorem certified0738 : Certified (graph core0738) (root 10) 2 2 :=
  of_native_maps core0738 DegreeOneMiddleResidualSpectrum1896.graph DegreeTwoThreeSpectrum5675.graph
    sourceMap0738 fusedMap0738 sourceMap0738_checked fusedMap0738_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0738
#print axioms sourceMap0738_checked
#print axioms fusedMap0738_checked
#print axioms certified0738
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
