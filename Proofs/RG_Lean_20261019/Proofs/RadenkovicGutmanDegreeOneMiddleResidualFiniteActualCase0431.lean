/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0431 : Family 9 := level9.get ⟨419,by decide⟩
def sourceMap0431 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0431 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0431_checked : acceptsGraphIso
    (source (graph core0431) (root 9) 2 2) DegreeOneMiddleResidualSpectrum820.graph sourceMap0431=true := by decide +kernel
theorem fusedMap0431_checked : acceptsGraphIso
    (fused (graph core0431) (root 9) 2 2) DegreeTwoThreeSpectrum4400.graph fusedMap0431=true := by decide +kernel
theorem certified0431 : Certified (graph core0431) (root 9) 2 2 :=
  of_native_maps core0431 DegreeOneMiddleResidualSpectrum820.graph DegreeTwoThreeSpectrum4400.graph
    sourceMap0431 fusedMap0431 sourceMap0431_checked fusedMap0431_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0431
#print axioms sourceMap0431_checked
#print axioms fusedMap0431_checked
#print axioms certified0431
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
