/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0603 : Family 10 := level10.get ⟨153,by decide⟩
def sourceMap0603 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,10,11,12,13,14,15,16,9,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0603 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0603_checked : acceptsGraphIso
    (source (graph core0603) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1891.graph sourceMap0603=true := by decide +kernel
theorem fusedMap0603_checked : acceptsGraphIso
    (fused (graph core0603) (root 10) 2 2) DegreeTwoThreeSpectrum5089.graph fusedMap0603=true := by decide +kernel
theorem certified0603 : Certified (graph core0603) (root 10) 2 2 :=
  of_native_maps core0603 DegreeOneMiddleResidualSpectrum1891.graph DegreeTwoThreeSpectrum5089.graph
    sourceMap0603 fusedMap0603 sourceMap0603_checked fusedMap0603_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0603
#print axioms sourceMap0603_checked
#print axioms fusedMap0603_checked
#print axioms certified0603
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
