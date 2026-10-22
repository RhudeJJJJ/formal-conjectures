/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0995 : Family 10 := level10.get ⟨878,by decide⟩
def sourceMap0995 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0995 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0995_checked : acceptsGraphIso
    (source (graph core0995) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2298.graph sourceMap0995=true := by decide +kernel
theorem fusedMap0995_checked : acceptsGraphIso
    (fused (graph core0995) (root 10) 2 2) DegreeTwoThreeSpectrum5728.graph fusedMap0995=true := by decide +kernel
theorem certified0995 : Certified (graph core0995) (root 10) 2 2 :=
  of_native_maps core0995 DegreeOneMiddleResidualSpectrum2298.graph DegreeTwoThreeSpectrum5728.graph
    sourceMap0995 fusedMap0995 sourceMap0995_checked fusedMap0995_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0995
#print axioms sourceMap0995_checked
#print axioms fusedMap0995_checked
#print axioms certified0995
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
