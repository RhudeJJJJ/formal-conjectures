/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0239 : Family 9 := level9.get ⟨280,by decide⟩
def sourceMap0239 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,6,7,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0239 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,5,6,4,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap0239_checked : acceptsGraphIso
    (source (graph core0239) (root 9) 0 0) DegreeOneSmallSpectrum649.graph sourceMap0239=true := by decide +kernel
theorem fusedMap0239_checked : acceptsGraphIso
    (fused (graph core0239) (root 9) 0 0) DegreeOneSmallSpectrum543.graph fusedMap0239=true := by decide +kernel
theorem certified0239 : Certified (graph core0239) (root 9) 0 0 :=
  of_native_maps core0239 DegreeOneSmallSpectrum649.graph DegreeOneSmallSpectrum543.graph
    sourceMap0239 fusedMap0239 sourceMap0239_checked fusedMap0239_checked
    DegreeTwoThreeFiniteComparisons.comparison0239
#print axioms sourceMap0239_checked
#print axioms fusedMap0239_checked
#print axioms certified0239
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
