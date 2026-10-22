/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0244 : Family 9 := level9.get ⟨57,by decide⟩
def sourceMap0244 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0244 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0244_checked : acceptsGraphIso
    (source (graph core0244) (root 9) 2 2) DegreeOneMiddleResidualSpectrum625.graph sourceMap0244=true := by decide +kernel
theorem fusedMap0244_checked : acceptsGraphIso
    (fused (graph core0244) (root 9) 2 2) DegreeTwoThreeSpectrum3953.graph fusedMap0244=true := by decide +kernel
theorem certified0244 : Certified (graph core0244) (root 9) 2 2 :=
  of_native_maps core0244 DegreeOneMiddleResidualSpectrum625.graph DegreeTwoThreeSpectrum3953.graph
    sourceMap0244 fusedMap0244 sourceMap0244_checked fusedMap0244_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0244
#print axioms sourceMap0244_checked
#print axioms fusedMap0244_checked
#print axioms certified0244
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
