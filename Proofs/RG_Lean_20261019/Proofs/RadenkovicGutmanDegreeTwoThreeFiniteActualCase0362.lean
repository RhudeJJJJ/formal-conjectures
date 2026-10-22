/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0362 : Family 9 := level9.get ⟨587,by decide⟩
def sourceMap0362 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,2,3,4] (sourceLabel 9 0 0 v)
def fusedMap0362 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0362_checked : acceptsGraphIso
    (source (graph core0362) (root 9) 0 0) DegreeOneSmallSpectrum843.graph sourceMap0362=true := by decide +kernel
theorem fusedMap0362_checked : acceptsGraphIso
    (fused (graph core0362) (root 9) 0 0) DegreeOneSmallSpectrum676.graph fusedMap0362=true := by decide +kernel
theorem certified0362 : Certified (graph core0362) (root 9) 0 0 :=
  of_native_maps core0362 DegreeOneSmallSpectrum843.graph DegreeOneSmallSpectrum676.graph
    sourceMap0362 fusedMap0362 sourceMap0362_checked fusedMap0362_checked
    DegreeTwoThreeFiniteComparisons.comparison0362
#print axioms sourceMap0362_checked
#print axioms fusedMap0362_checked
#print axioms certified0362
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
