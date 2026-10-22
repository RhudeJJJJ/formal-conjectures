/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0908 : Family 10 := level10.get ⟨695,by decide⟩
def sourceMap0908 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0908 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0908_checked : acceptsGraphIso
    (source (graph core0908) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2164.graph sourceMap0908=true := by decide +kernel
theorem fusedMap0908_checked : acceptsGraphIso
    (fused (graph core0908) (root 10) 2 2) DegreeTwoThreeSpectrum5432.graph fusedMap0908=true := by decide +kernel
theorem certified0908 : Certified (graph core0908) (root 10) 2 2 :=
  of_native_maps core0908 DegreeOneMiddleResidualSpectrum2164.graph DegreeTwoThreeSpectrum5432.graph
    sourceMap0908 fusedMap0908 sourceMap0908_checked fusedMap0908_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0908
#print axioms sourceMap0908_checked
#print axioms fusedMap0908_checked
#print axioms certified0908
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
