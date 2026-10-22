/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0909 : Family 10 := level10.get ⟨696,by decide⟩
def sourceMap0909 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0909 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0909_checked : acceptsGraphIso
    (source (graph core0909) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2165.graph sourceMap0909=true := by decide +kernel
theorem fusedMap0909_checked : acceptsGraphIso
    (fused (graph core0909) (root 10) 2 2) DegreeTwoThreeSpectrum5433.graph fusedMap0909=true := by decide +kernel
theorem certified0909 : Certified (graph core0909) (root 10) 2 2 :=
  of_native_maps core0909 DegreeOneMiddleResidualSpectrum2165.graph DegreeTwoThreeSpectrum5433.graph
    sourceMap0909 fusedMap0909 sourceMap0909_checked fusedMap0909_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0909
#print axioms sourceMap0909_checked
#print axioms fusedMap0909_checked
#print axioms certified0909
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
