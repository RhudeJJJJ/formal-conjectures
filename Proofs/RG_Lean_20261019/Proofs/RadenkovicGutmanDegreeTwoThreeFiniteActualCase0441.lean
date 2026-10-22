/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0441 : Family 10 := level10.get ⟨186,by decide⟩
def sourceMap0441 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0441 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0441_checked : acceptsGraphIso
    (source (graph core0441) (root 10) 0 0) DegreeOneSmallSpectrum872.graph sourceMap0441=true := by decide +kernel
theorem fusedMap0441_checked : acceptsGraphIso
    (fused (graph core0441) (root 10) 0 0) DegreeOneSmallSpectrum871.graph fusedMap0441=true := by decide +kernel
theorem certified0441 : Certified (graph core0441) (root 10) 0 0 :=
  of_native_maps core0441 DegreeOneSmallSpectrum872.graph DegreeOneSmallSpectrum871.graph
    sourceMap0441 fusedMap0441 sourceMap0441_checked fusedMap0441_checked
    DegreeTwoThreeFiniteComparisons.comparison0441
#print axioms sourceMap0441_checked
#print axioms fusedMap0441_checked
#print axioms certified0441
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
