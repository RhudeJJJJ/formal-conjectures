/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0146 : Family 8 := level8.get ⟨234,by decide⟩
def sourceMap0146 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (sourceLabel 8 0 0 v)
def fusedMap0146 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0146_checked : acceptsGraphIso
    (source (graph core0146) (root 8) 0 0) DegreeTwoThreeSpectrum285.graph sourceMap0146=true := by decide +kernel
theorem fusedMap0146_checked : acceptsGraphIso
    (fused (graph core0146) (root 8) 0 0) DegreeOneSmallSpectrum322.graph fusedMap0146=true := by decide +kernel
theorem certified0146 : Certified (graph core0146) (root 8) 0 0 :=
  of_native_maps core0146 DegreeTwoThreeSpectrum285.graph DegreeOneSmallSpectrum322.graph
    sourceMap0146 fusedMap0146 sourceMap0146_checked fusedMap0146_checked
    DegreeTwoThreeFiniteComparisons.comparison0146
#print axioms sourceMap0146_checked
#print axioms fusedMap0146_checked
#print axioms certified0146
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
