/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0880 : Family 10 := level10.get ⟨628,by decide⟩
def sourceMap0880 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0880 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0880_checked : acceptsGraphIso
    (source (graph core0880) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2122.graph sourceMap0880=true := by decide +kernel
theorem fusedMap0880_checked : acceptsGraphIso
    (fused (graph core0880) (root 10) 2 2) DegreeTwoThreeSpectrum5319.graph fusedMap0880=true := by decide +kernel
theorem certified0880 : Certified (graph core0880) (root 10) 2 2 :=
  of_native_maps core0880 DegreeOneMiddleResidualSpectrum2122.graph DegreeTwoThreeSpectrum5319.graph
    sourceMap0880 fusedMap0880 sourceMap0880_checked fusedMap0880_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0880
#print axioms sourceMap0880_checked
#print axioms fusedMap0880_checked
#print axioms certified0880
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
