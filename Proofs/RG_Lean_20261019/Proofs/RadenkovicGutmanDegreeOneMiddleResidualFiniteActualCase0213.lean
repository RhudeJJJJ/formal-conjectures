/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0213 : Family 9 := level9.get ⟨17,by decide⟩
def sourceMap0213 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0213 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0213_checked : acceptsGraphIso
    (source (graph core0213) (root 9) 2 2) DegreeOneMiddleResidualSpectrum667.graph sourceMap0213=true := by decide +kernel
theorem fusedMap0213_checked : acceptsGraphIso
    (fused (graph core0213) (root 9) 2 2) DegreeTwoThreeSpectrum3863.graph fusedMap0213=true := by decide +kernel
theorem certified0213 : Certified (graph core0213) (root 9) 2 2 :=
  of_native_maps core0213 DegreeOneMiddleResidualSpectrum667.graph DegreeTwoThreeSpectrum3863.graph
    sourceMap0213 fusedMap0213 sourceMap0213_checked fusedMap0213_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0213
#print axioms sourceMap0213_checked
#print axioms fusedMap0213_checked
#print axioms certified0213
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
