/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0681 : Family 10 := level10.get ⟨274,by decide⟩
def sourceMap0681 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,6,0,1,2,3,4,5,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap0681 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0681_checked : acceptsGraphIso
    (source (graph core0681) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1700.graph sourceMap0681=true := by decide +kernel
theorem fusedMap0681_checked : acceptsGraphIso
    (fused (graph core0681) (root 10) 2 2) DegreeTwoThreeSpectrum5404.graph fusedMap0681=true := by decide +kernel
theorem certified0681 : Certified (graph core0681) (root 10) 2 2 :=
  of_native_maps core0681 DegreeOneMiddleResidualSpectrum1700.graph DegreeTwoThreeSpectrum5404.graph
    sourceMap0681 fusedMap0681 sourceMap0681_checked fusedMap0681_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0681
#print axioms sourceMap0681_checked
#print axioms fusedMap0681_checked
#print axioms certified0681
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
