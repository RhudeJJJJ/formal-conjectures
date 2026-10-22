/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0244 : Family 9 := level9.get ⟨294,by decide⟩
def sourceMap0244 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,9,10,11,6,7,8,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0244 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,5,6,7,4,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap0244_checked : acceptsGraphIso
    (source (graph core0244) (root 9) 0 0) DegreeOneSmallSpectrum630.graph sourceMap0244=true := by decide +kernel
theorem fusedMap0244_checked : acceptsGraphIso
    (fused (graph core0244) (root 9) 0 0) DegreeOneSmallSpectrum536.graph fusedMap0244=true := by decide +kernel
theorem certified0244 : Certified (graph core0244) (root 9) 0 0 :=
  of_native_maps core0244 DegreeOneSmallSpectrum630.graph DegreeOneSmallSpectrum536.graph
    sourceMap0244 fusedMap0244 sourceMap0244_checked fusedMap0244_checked
    DegreeTwoThreeFiniteComparisons.comparison0244
#print axioms sourceMap0244_checked
#print axioms fusedMap0244_checked
#print axioms certified0244
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
