/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0089 : Family 8 := level8.get ⟨92,by decide⟩
def sourceMap0089 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,2,3,4,5,6] (sourceLabel 8 0 0 v)
def fusedMap0089 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,2,3,4,5,6] (fusedLabel 8 0 0 v)
theorem sourceMap0089_checked : acceptsGraphIso
    (source (graph core0089) (root 8) 0 0) DegreeOneSmallSpectrum177.graph sourceMap0089=true := by decide +kernel
theorem fusedMap0089_checked : acceptsGraphIso
    (fused (graph core0089) (root 8) 0 0) DegreeOneSmallSpectrum176.graph fusedMap0089=true := by decide +kernel
theorem certified0089 : Certified (graph core0089) (root 8) 0 0 :=
  of_native_maps core0089 DegreeOneSmallSpectrum177.graph DegreeOneSmallSpectrum176.graph
    sourceMap0089 fusedMap0089 sourceMap0089_checked fusedMap0089_checked
    DegreeTwoThreeFiniteComparisons.comparison0089
#print axioms sourceMap0089_checked
#print axioms fusedMap0089_checked
#print axioms certified0089
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
