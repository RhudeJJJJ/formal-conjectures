/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0134 : Family 8 := level8.get ⟨208,by decide⟩
def sourceMap0134 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,5,6,7,8,9,10,2,3,4] (sourceLabel 8 0 0 v)
def fusedMap0134 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap0134_checked : acceptsGraphIso
    (source (graph core0134) (root 8) 0 0) DegreeOneSmallSpectrum359.graph sourceMap0134=true := by decide +kernel
theorem fusedMap0134_checked : acceptsGraphIso
    (fused (graph core0134) (root 8) 0 0) DegreeOneSmallSpectrum269.graph fusedMap0134=true := by decide +kernel
theorem certified0134 : Certified (graph core0134) (root 8) 0 0 :=
  of_native_maps core0134 DegreeOneSmallSpectrum359.graph DegreeOneSmallSpectrum269.graph
    sourceMap0134 fusedMap0134 sourceMap0134_checked fusedMap0134_checked
    DegreeTwoThreeFiniteComparisons.comparison0134
#print axioms sourceMap0134_checked
#print axioms fusedMap0134_checked
#print axioms certified0134
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
