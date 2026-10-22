/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0351 : Family 9 := level9.get ⟨558,by decide⟩
def sourceMap0351 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0351 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0351_checked : acceptsGraphIso
    (source (graph core0351) (root 9) 0 0) DegreeOneSmallSpectrum619.graph sourceMap0351=true := by decide +kernel
theorem fusedMap0351_checked : acceptsGraphIso
    (fused (graph core0351) (root 9) 0 0) DegreeOneSmallSpectrum618.graph fusedMap0351=true := by decide +kernel
theorem certified0351 : Certified (graph core0351) (root 9) 0 0 :=
  of_native_maps core0351 DegreeOneSmallSpectrum619.graph DegreeOneSmallSpectrum618.graph
    sourceMap0351 fusedMap0351 sourceMap0351_checked fusedMap0351_checked
    DegreeTwoThreeFiniteComparisons.comparison0351
#print axioms sourceMap0351_checked
#print axioms fusedMap0351_checked
#print axioms certified0351
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
