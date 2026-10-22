/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0829 : Family 10 := level10.get ⟨537,by decide⟩
def sourceMap0829 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0829 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0829_checked : acceptsGraphIso
    (source (graph core0829) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2027.graph sourceMap0829=true := by decide +kernel
theorem fusedMap0829_checked : acceptsGraphIso
    (fused (graph core0829) (root 10) 2 2) DegreeTwoThreeSpectrum5186.graph fusedMap0829=true := by decide +kernel
theorem certified0829 : Certified (graph core0829) (root 10) 2 2 :=
  of_native_maps core0829 DegreeOneMiddleResidualSpectrum2027.graph DegreeTwoThreeSpectrum5186.graph
    sourceMap0829 fusedMap0829 sourceMap0829_checked fusedMap0829_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0829
#print axioms sourceMap0829_checked
#print axioms fusedMap0829_checked
#print axioms certified0829
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
