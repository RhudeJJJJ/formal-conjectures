/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0269 : Family 9 := level9.get ⟨360,by decide⟩
def sourceMap0269 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,2,3,4] (sourceLabel 9 0 0 v)
def fusedMap0269 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0269_checked : acceptsGraphIso
    (source (graph core0269) (root 9) 0 0) DegreeOneSmallSpectrum659.graph sourceMap0269=true := by decide +kernel
theorem fusedMap0269_checked : acceptsGraphIso
    (fused (graph core0269) (root 9) 0 0) DegreeOneSmallSpectrum696.graph fusedMap0269=true := by decide +kernel
theorem certified0269 : Certified (graph core0269) (root 9) 0 0 :=
  of_native_maps core0269 DegreeOneSmallSpectrum659.graph DegreeOneSmallSpectrum696.graph
    sourceMap0269 fusedMap0269 sourceMap0269_checked fusedMap0269_checked
    DegreeTwoThreeFiniteComparisons.comparison0269
#print axioms sourceMap0269_checked
#print axioms fusedMap0269_checked
#print axioms certified0269
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
