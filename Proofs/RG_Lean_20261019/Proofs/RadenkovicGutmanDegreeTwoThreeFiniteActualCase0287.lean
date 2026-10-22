/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0287 : Family 9 := level9.get ⟨403,by decide⟩
def sourceMap0287 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,2,3,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap0287 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,2,3,4,5,6] (fusedLabel 9 0 0 v)
theorem sourceMap0287_checked : acceptsGraphIso
    (source (graph core0287) (root 9) 0 0) DegreeOneSmallSpectrum721.graph sourceMap0287=true := by decide +kernel
theorem fusedMap0287_checked : acceptsGraphIso
    (fused (graph core0287) (root 9) 0 0) DegreeOneSmallSpectrum701.graph fusedMap0287=true := by decide +kernel
theorem certified0287 : Certified (graph core0287) (root 9) 0 0 :=
  of_native_maps core0287 DegreeOneSmallSpectrum721.graph DegreeOneSmallSpectrum701.graph
    sourceMap0287 fusedMap0287 sourceMap0287_checked fusedMap0287_checked
    DegreeTwoThreeFiniteComparisons.comparison0287
#print axioms sourceMap0287_checked
#print axioms fusedMap0287_checked
#print axioms certified0287
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
