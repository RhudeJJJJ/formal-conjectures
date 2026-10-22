/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0602 : Family 10 := level10.get ⟨152,by decide⟩
def sourceMap0602 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,9,10,11,12,13,14,15,16,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0602 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0602_checked : acceptsGraphIso
    (source (graph core0602) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1938.graph sourceMap0602=true := by decide +kernel
theorem fusedMap0602_checked : acceptsGraphIso
    (fused (graph core0602) (root 10) 2 2) DegreeTwoThreeSpectrum5088.graph fusedMap0602=true := by decide +kernel
theorem certified0602 : Certified (graph core0602) (root 10) 2 2 :=
  of_native_maps core0602 DegreeOneMiddleResidualSpectrum1938.graph DegreeTwoThreeSpectrum5088.graph
    sourceMap0602 fusedMap0602 sourceMap0602_checked fusedMap0602_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0602
#print axioms sourceMap0602_checked
#print axioms fusedMap0602_checked
#print axioms certified0602
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
