/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0086 : Family 8 := level8.get ⟨88,by decide⟩
def sourceMap0086 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,8,9,10,6,7,3,4,5] (sourceLabel 8 0 0 v)
def fusedMap0086 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,5,6,4,2,3] (fusedLabel 8 0 0 v)
theorem sourceMap0086_checked : acceptsGraphIso
    (source (graph core0086) (root 8) 0 0) DegreeOneSmallSpectrum253.graph sourceMap0086=true := by decide +kernel
theorem fusedMap0086_checked : acceptsGraphIso
    (fused (graph core0086) (root 8) 0 0) DegreeOneSmallSpectrum209.graph fusedMap0086=true := by decide +kernel
theorem certified0086 : Certified (graph core0086) (root 8) 0 0 :=
  of_native_maps core0086 DegreeOneSmallSpectrum253.graph DegreeOneSmallSpectrum209.graph
    sourceMap0086 fusedMap0086 sourceMap0086_checked fusedMap0086_checked
    DegreeTwoThreeFiniteComparisons.comparison0086
#print axioms sourceMap0086_checked
#print axioms fusedMap0086_checked
#print axioms certified0086
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
