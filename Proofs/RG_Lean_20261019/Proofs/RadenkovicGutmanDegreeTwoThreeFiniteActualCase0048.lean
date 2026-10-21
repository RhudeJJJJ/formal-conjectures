/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0048 : Family 7 := level7.get ⟨68,by decide⟩
def sourceMap0048 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![5,0,1,2,3,4,6,7,8,9] (sourceLabel 7 0 0 v)
def fusedMap0048 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![5,0,1,2,3,4,6,7,8,9] (fusedLabel 7 0 0 v)
theorem sourceMap0048_checked : acceptsGraphIso
    (source (graph core0048) (root 7) 0 0) DegreeTwoThreeSpectrum099.graph sourceMap0048=true := by decide +kernel
theorem fusedMap0048_checked : acceptsGraphIso
    (fused (graph core0048) (root 7) 0 0) DegreeOneSmallSpectrum104.graph fusedMap0048=true := by decide +kernel
theorem certified0048 : Certified (graph core0048) (root 7) 0 0 :=
  of_native_maps core0048 DegreeTwoThreeSpectrum099.graph DegreeOneSmallSpectrum104.graph
    sourceMap0048 fusedMap0048 sourceMap0048_checked fusedMap0048_checked
    DegreeTwoThreeFiniteComparisons.comparison0048
#print axioms sourceMap0048_checked
#print axioms fusedMap0048_checked
#print axioms certified0048
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
