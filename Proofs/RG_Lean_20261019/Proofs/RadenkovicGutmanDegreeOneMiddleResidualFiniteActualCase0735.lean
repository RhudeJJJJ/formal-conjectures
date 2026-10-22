/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0735 : Family 10 := level10.get ⟨367,by decide⟩
def sourceMap0735 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0735 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0735_checked : acceptsGraphIso
    (source (graph core0735) (root 10) 2 2) DegreeTwoThreeSpectrum6837.graph sourceMap0735=true := by decide +kernel
theorem fusedMap0735_checked : acceptsGraphIso
    (fused (graph core0735) (root 10) 2 2) DegreeTwoThreeSpectrum5661.graph fusedMap0735=true := by decide +kernel
theorem certified0735 : Certified (graph core0735) (root 10) 2 2 :=
  of_native_maps core0735 DegreeTwoThreeSpectrum6837.graph DegreeTwoThreeSpectrum5661.graph
    sourceMap0735 fusedMap0735 sourceMap0735_checked fusedMap0735_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0735
#print axioms sourceMap0735_checked
#print axioms fusedMap0735_checked
#print axioms certified0735
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
