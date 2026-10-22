/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0096 : Family 8 := level8.get ⟨48,by decide⟩
def sourceMap0096 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,13,14,7,8,9,10,11,12] (sourceLabel 8 2 2 v)
def fusedMap0096 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0096_checked : acceptsGraphIso
    (source (graph core0096) (root 8) 2 2) DegreeOneMiddleResidualSpectrum296.graph sourceMap0096=true := by decide +kernel
theorem fusedMap0096_checked : acceptsGraphIso
    (fused (graph core0096) (root 8) 2 2) DegreeTwoThreeSpectrum2334.graph fusedMap0096=true := by decide +kernel
theorem certified0096 : Certified (graph core0096) (root 8) 2 2 :=
  of_native_maps core0096 DegreeOneMiddleResidualSpectrum296.graph DegreeTwoThreeSpectrum2334.graph
    sourceMap0096 fusedMap0096 sourceMap0096_checked fusedMap0096_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0096
#print axioms sourceMap0096_checked
#print axioms fusedMap0096_checked
#print axioms certified0096
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
