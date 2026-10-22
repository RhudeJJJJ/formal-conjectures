/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0798 : Family 10 := level10.get ⟨475,by decide⟩
def sourceMap0798 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,12,13,14,15,16,8,9,10,11,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0798 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0798_checked : acceptsGraphIso
    (source (graph core0798) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1849.graph sourceMap0798=true := by decide +kernel
theorem fusedMap0798_checked : acceptsGraphIso
    (fused (graph core0798) (root 10) 2 2) DegreeTwoThreeSpectrum5936.graph fusedMap0798=true := by decide +kernel
theorem certified0798 : Certified (graph core0798) (root 10) 2 2 :=
  of_native_maps core0798 DegreeOneMiddleResidualSpectrum1849.graph DegreeTwoThreeSpectrum5936.graph
    sourceMap0798 fusedMap0798 sourceMap0798_checked fusedMap0798_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0798
#print axioms sourceMap0798_checked
#print axioms fusedMap0798_checked
#print axioms certified0798
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
