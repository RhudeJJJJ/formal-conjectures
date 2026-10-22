/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0084 : Family 8 := level8.get ⟨81,by decide⟩
def sourceMap0084 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,2,3,4,5] (sourceLabel 8 0 0 v)
def fusedMap0084 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,2,3,4,5] (fusedLabel 8 0 0 v)
theorem sourceMap0084_checked : acceptsGraphIso
    (source (graph core0084) (root 8) 0 0) DegreeOneSmallSpectrum206.graph sourceMap0084=true := by decide +kernel
theorem fusedMap0084_checked : acceptsGraphIso
    (fused (graph core0084) (root 8) 0 0) DegreeOneSmallSpectrum201.graph fusedMap0084=true := by decide +kernel
theorem certified0084 : Certified (graph core0084) (root 8) 0 0 :=
  of_native_maps core0084 DegreeOneSmallSpectrum206.graph DegreeOneSmallSpectrum201.graph
    sourceMap0084 fusedMap0084 sourceMap0084_checked fusedMap0084_checked
    DegreeTwoThreeFiniteComparisons.comparison0084
#print axioms sourceMap0084_checked
#print axioms fusedMap0084_checked
#print axioms certified0084
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
