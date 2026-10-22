/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0980 : Family 10 := level10.get ⟨845,by decide⟩
def sourceMap0980 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0980 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0980_checked : acceptsGraphIso
    (source (graph core0980) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2279.graph sourceMap0980=true := by decide +kernel
theorem fusedMap0980_checked : acceptsGraphIso
    (fused (graph core0980) (root 10) 2 2) DegreeTwoThreeSpectrum5677.graph fusedMap0980=true := by decide +kernel
theorem certified0980 : Certified (graph core0980) (root 10) 2 2 :=
  of_native_maps core0980 DegreeOneMiddleResidualSpectrum2279.graph DegreeTwoThreeSpectrum5677.graph
    sourceMap0980 fusedMap0980 sourceMap0980_checked fusedMap0980_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0980
#print axioms sourceMap0980_checked
#print axioms fusedMap0980_checked
#print axioms certified0980
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
