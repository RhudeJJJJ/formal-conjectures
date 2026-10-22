/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0082 : Family 8 := level8.get ⟨77,by decide⟩
def sourceMap0082 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,6,7,8,9,10,3,4,5] (sourceLabel 8 0 0 v)
def fusedMap0082 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,5,6,7,8,9,10,4,2,3] (fusedLabel 8 0 0 v)
theorem sourceMap0082_checked : acceptsGraphIso
    (source (graph core0082) (root 8) 0 0) DegreeOneSmallSpectrum266.graph sourceMap0082=true := by decide +kernel
theorem fusedMap0082_checked : acceptsGraphIso
    (fused (graph core0082) (root 8) 0 0) DegreeOneSmallSpectrum215.graph fusedMap0082=true := by decide +kernel
theorem certified0082 : Certified (graph core0082) (root 8) 0 0 :=
  of_native_maps core0082 DegreeOneSmallSpectrum266.graph DegreeOneSmallSpectrum215.graph
    sourceMap0082 fusedMap0082 sourceMap0082_checked fusedMap0082_checked
    DegreeTwoThreeFiniteComparisons.comparison0082
#print axioms sourceMap0082_checked
#print axioms fusedMap0082_checked
#print axioms certified0082
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
