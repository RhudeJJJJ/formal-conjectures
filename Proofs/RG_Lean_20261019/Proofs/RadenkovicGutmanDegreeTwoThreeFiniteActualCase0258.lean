/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0258 : Family 9 := level9.get ⟨328,by decide⟩
def sourceMap0258 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0258 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0258_checked : acceptsGraphIso
    (source (graph core0258) (root 9) 0 0) DegreeTwoThreeSpectrum530.graph sourceMap0258=true := by decide +kernel
theorem fusedMap0258_checked : acceptsGraphIso
    (fused (graph core0258) (root 9) 0 0) DegreeOneSmallSpectrum622.graph fusedMap0258=true := by decide +kernel
theorem certified0258 : Certified (graph core0258) (root 9) 0 0 :=
  of_native_maps core0258 DegreeTwoThreeSpectrum530.graph DegreeOneSmallSpectrum622.graph
    sourceMap0258 fusedMap0258 sourceMap0258_checked fusedMap0258_checked
    DegreeTwoThreeFiniteComparisons.comparison0258
#print axioms sourceMap0258_checked
#print axioms fusedMap0258_checked
#print axioms certified0258
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
