/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0337 : Family 9 := level9.get ⟨519,by decide⟩
def sourceMap0337 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,7,8,9,10,11,1,2,3,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap0337 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,7,8,9,10,11,1,2,3,4,5,6] (fusedLabel 9 0 0 v)
theorem sourceMap0337_checked : acceptsGraphIso
    (source (graph core0337) (root 9) 0 0) DegreeOneSmallSpectrum543.graph sourceMap0337=true := by decide +kernel
theorem fusedMap0337_checked : acceptsGraphIso
    (fused (graph core0337) (root 9) 0 0) DegreeOneSmallSpectrum539.graph fusedMap0337=true := by decide +kernel
theorem certified0337 : Certified (graph core0337) (root 9) 0 0 :=
  of_native_maps core0337 DegreeOneSmallSpectrum543.graph DegreeOneSmallSpectrum539.graph
    sourceMap0337 fusedMap0337 sourceMap0337_checked fusedMap0337_checked
    DegreeTwoThreeFiniteComparisons.comparison0337
#print axioms sourceMap0337_checked
#print axioms fusedMap0337_checked
#print axioms certified0337
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
