/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0075 : Family 8 := level8.get ⟨18,by decide⟩
def sourceMap0075 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,6,0,1,2,3,4,5,14,8,9,10,11,12,13] (sourceLabel 8 2 2 v)
def fusedMap0075 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0075_checked : acceptsGraphIso
    (source (graph core0075) (root 8) 2 2) DegreeOneMiddleResidualSpectrum231.graph sourceMap0075=true := by decide +kernel
theorem fusedMap0075_checked : acceptsGraphIso
    (fused (graph core0075) (root 8) 2 2) DegreeTwoThreeSpectrum2374.graph fusedMap0075=true := by decide +kernel
theorem certified0075 : Certified (graph core0075) (root 8) 2 2 :=
  of_native_maps core0075 DegreeOneMiddleResidualSpectrum231.graph DegreeTwoThreeSpectrum2374.graph
    sourceMap0075 fusedMap0075 sourceMap0075_checked fusedMap0075_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0075
#print axioms sourceMap0075_checked
#print axioms fusedMap0075_checked
#print axioms certified0075
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
