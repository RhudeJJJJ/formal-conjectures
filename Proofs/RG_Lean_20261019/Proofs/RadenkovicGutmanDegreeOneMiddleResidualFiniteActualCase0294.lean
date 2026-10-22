/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0294 : Family 9 := level9.get ⟨138,by decide⟩
def sourceMap0294 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0294 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0294_checked : acceptsGraphIso
    (source (graph core0294) (root 9) 2 2) DegreeOneMiddleResidualSpectrum744.graph sourceMap0294=true := by decide +kernel
theorem fusedMap0294_checked : acceptsGraphIso
    (fused (graph core0294) (root 9) 2 2) DegreeTwoThreeSpectrum3893.graph fusedMap0294=true := by decide +kernel
theorem certified0294 : Certified (graph core0294) (root 9) 2 2 :=
  of_native_maps core0294 DegreeOneMiddleResidualSpectrum744.graph DegreeTwoThreeSpectrum3893.graph
    sourceMap0294 fusedMap0294 sourceMap0294_checked fusedMap0294_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0294
#print axioms sourceMap0294_checked
#print axioms fusedMap0294_checked
#print axioms certified0294
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
