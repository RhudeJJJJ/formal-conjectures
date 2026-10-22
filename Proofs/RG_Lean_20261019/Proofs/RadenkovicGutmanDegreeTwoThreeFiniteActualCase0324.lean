/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0324 : Family 9 := level9.get ⟨496,by decide⟩
def sourceMap0324 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,9,10,11,5,6,7,8,2,3,4] (sourceLabel 9 0 0 v)
def fusedMap0324 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,4,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap0324_checked : acceptsGraphIso
    (source (graph core0324) (root 9) 0 0) DegreeOneSmallSpectrum627.graph sourceMap0324=true := by decide +kernel
theorem fusedMap0324_checked : acceptsGraphIso
    (fused (graph core0324) (root 9) 0 0) DegreeOneSmallSpectrum818.graph fusedMap0324=true := by decide +kernel
theorem certified0324 : Certified (graph core0324) (root 9) 0 0 :=
  of_native_maps core0324 DegreeOneSmallSpectrum627.graph DegreeOneSmallSpectrum818.graph
    sourceMap0324 fusedMap0324 sourceMap0324_checked fusedMap0324_checked
    DegreeTwoThreeFiniteComparisons.comparison0324
#print axioms sourceMap0324_checked
#print axioms fusedMap0324_checked
#print axioms certified0324
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
