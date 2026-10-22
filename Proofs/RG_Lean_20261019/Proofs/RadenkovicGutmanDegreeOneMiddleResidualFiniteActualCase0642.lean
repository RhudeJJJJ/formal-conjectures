/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0642 : Family 10 := level10.get ⟨217,by decide⟩
def sourceMap0642 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0642 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0642_checked : acceptsGraphIso
    (source (graph core0642) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1616.graph sourceMap0642=true := by decide +kernel
theorem fusedMap0642_checked : acceptsGraphIso
    (fused (graph core0642) (root 10) 2 2) DegreeTwoThreeSpectrum5237.graph fusedMap0642=true := by decide +kernel
theorem certified0642 : Certified (graph core0642) (root 10) 2 2 :=
  of_native_maps core0642 DegreeOneMiddleResidualSpectrum1616.graph DegreeTwoThreeSpectrum5237.graph
    sourceMap0642 fusedMap0642 sourceMap0642_checked fusedMap0642_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0642
#print axioms sourceMap0642_checked
#print axioms fusedMap0642_checked
#print axioms certified0642
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
