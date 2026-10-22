/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0318 : Family 9 := level9.get ⟨478,by decide⟩
def sourceMap0318 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,7,8,9,10,11,1,2,3,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap0318 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,7,8,9,10,11,1,2,3,4,5,6] (fusedLabel 9 0 0 v)
theorem sourceMap0318_checked : acceptsGraphIso
    (source (graph core0318) (root 9) 0 0) DegreeOneSmallSpectrum467.graph sourceMap0318=true := by decide +kernel
theorem fusedMap0318_checked : acceptsGraphIso
    (fused (graph core0318) (root 9) 0 0) DegreeOneSmallSpectrum462.graph fusedMap0318=true := by decide +kernel
theorem certified0318 : Certified (graph core0318) (root 9) 0 0 :=
  of_native_maps core0318 DegreeOneSmallSpectrum467.graph DegreeOneSmallSpectrum462.graph
    sourceMap0318 fusedMap0318 sourceMap0318_checked fusedMap0318_checked
    DegreeTwoThreeFiniteComparisons.comparison0318
#print axioms sourceMap0318_checked
#print axioms fusedMap0318_checked
#print axioms certified0318
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
