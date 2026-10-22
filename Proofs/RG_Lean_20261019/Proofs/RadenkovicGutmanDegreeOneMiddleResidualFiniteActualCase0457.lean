/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0457 : Family 9 := level9.get ⟨494,by decide⟩
def sourceMap0457 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,7,8,9,10,11,12,13,14,15,1,2,3,4,5,6] (sourceLabel 9 2 2 v)
def fusedMap0457 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0457_checked : acceptsGraphIso
    (source (graph core0457) (root 9) 2 2) DegreeOneMiddleResidualSpectrum877.graph sourceMap0457=true := by decide +kernel
theorem fusedMap0457_checked : acceptsGraphIso
    (fused (graph core0457) (root 9) 2 2) DegreeTwoThreeSpectrum4570.graph fusedMap0457=true := by decide +kernel
theorem certified0457 : Certified (graph core0457) (root 9) 2 2 :=
  of_native_maps core0457 DegreeOneMiddleResidualSpectrum877.graph DegreeTwoThreeSpectrum4570.graph
    sourceMap0457 fusedMap0457 sourceMap0457_checked fusedMap0457_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0457
#print axioms sourceMap0457_checked
#print axioms fusedMap0457_checked
#print axioms certified0457
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
