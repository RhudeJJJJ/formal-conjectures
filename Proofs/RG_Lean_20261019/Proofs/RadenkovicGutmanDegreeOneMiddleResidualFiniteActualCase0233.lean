/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0233 : Family 9 := level9.get ⟨44,by decide⟩
def sourceMap0233 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0233 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0233_checked : acceptsGraphIso
    (source (graph core0233) (root 9) 2 2) DegreeOneMiddleResidualSpectrum580.graph sourceMap0233=true := by decide +kernel
theorem fusedMap0233_checked : acceptsGraphIso
    (fused (graph core0233) (root 9) 2 2) DegreeTwoThreeSpectrum3902.graph fusedMap0233=true := by decide +kernel
theorem certified0233 : Certified (graph core0233) (root 9) 2 2 :=
  of_native_maps core0233 DegreeOneMiddleResidualSpectrum580.graph DegreeTwoThreeSpectrum3902.graph
    sourceMap0233 fusedMap0233 sourceMap0233_checked fusedMap0233_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0233
#print axioms sourceMap0233_checked
#print axioms fusedMap0233_checked
#print axioms certified0233
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
