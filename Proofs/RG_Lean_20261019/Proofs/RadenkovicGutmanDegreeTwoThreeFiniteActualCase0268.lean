/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0268 : Family 9 := level9.get ⟨356,by decide⟩
def sourceMap0268 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,2,3,4] (sourceLabel 9 0 0 v)
def fusedMap0268 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0268_checked : acceptsGraphIso
    (source (graph core0268) (root 9) 0 0) DegreeOneSmallSpectrum658.graph sourceMap0268=true := by decide +kernel
theorem fusedMap0268_checked : acceptsGraphIso
    (fused (graph core0268) (root 9) 0 0) DegreeOneSmallSpectrum682.graph fusedMap0268=true := by decide +kernel
theorem certified0268 : Certified (graph core0268) (root 9) 0 0 :=
  of_native_maps core0268 DegreeOneSmallSpectrum658.graph DegreeOneSmallSpectrum682.graph
    sourceMap0268 fusedMap0268 sourceMap0268_checked fusedMap0268_checked
    DegreeTwoThreeFiniteComparisons.comparison0268
#print axioms sourceMap0268_checked
#print axioms fusedMap0268_checked
#print axioms certified0268
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
