/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0119 : Family 8 := level8.get ⟨85,by decide⟩
def sourceMap0119 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,2,3,4,5,6,7] (sourceLabel 8 2 2 v)
def fusedMap0119 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0119_checked : acceptsGraphIso
    (source (graph core0119) (root 8) 2 2) DegreeOneMiddleResidualSpectrum340.graph sourceMap0119=true := by decide +kernel
theorem fusedMap0119_checked : acceptsGraphIso
    (fused (graph core0119) (root 8) 2 2) DegreeTwoThreeSpectrum2410.graph fusedMap0119=true := by decide +kernel
theorem certified0119 : Certified (graph core0119) (root 8) 2 2 :=
  of_native_maps core0119 DegreeOneMiddleResidualSpectrum340.graph DegreeTwoThreeSpectrum2410.graph
    sourceMap0119 fusedMap0119 sourceMap0119_checked fusedMap0119_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0119
#print axioms sourceMap0119_checked
#print axioms fusedMap0119_checked
#print axioms certified0119
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
