/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0972 : Family 8 := level8.get ⟨84,by decide⟩
def sourceMap0972 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,5,6,7,4,2,3] (sourceLabel 8 0 1 v)
def fusedMap0972 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,2,3,4] (fusedLabel 8 0 1 v)
theorem sourceMap0972_checked : acceptsGraphIso
    (source (graph core0972) (root 8) 0 1) DegreeOneSmallSpectrum536.graph sourceMap0972=true := by decide +kernel
theorem fusedMap0972_checked : acceptsGraphIso
    (fused (graph core0972) (root 8) 0 1) DegreeOneSmallSpectrum586.graph fusedMap0972=true := by decide +kernel
theorem certified0972 : Certified (graph core0972) (root 8) 0 1 :=
  of_native_maps core0972 DegreeOneSmallSpectrum536.graph DegreeOneSmallSpectrum586.graph
    sourceMap0972 fusedMap0972 sourceMap0972_checked fusedMap0972_checked
    DegreeOneSmallComparisons.comparison0972
#print axioms sourceMap0972_checked
#print axioms fusedMap0972_checked
#print axioms certified0972
def sourceMap0972swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,5,6,7,2,3,4] (sourceLabel 8 1 0 v)
def fusedMap0972swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,2,3,4] (fusedLabel 8 1 0 v)
theorem sourceMap0972swap_checked : acceptsGraphIso
    (source (graph core0972) (root 8) 1 0) DegreeOneSmallSpectrum536.graph sourceMap0972swap=true := by decide +kernel
theorem fusedMap0972swap_checked : acceptsGraphIso
    (fused (graph core0972) (root 8) 1 0) DegreeOneSmallSpectrum586.graph fusedMap0972swap=true := by decide +kernel
theorem certified0972swap : Certified (graph core0972) (root 8) 1 0 :=
  of_native_maps core0972 DegreeOneSmallSpectrum536.graph DegreeOneSmallSpectrum586.graph
    sourceMap0972swap fusedMap0972swap sourceMap0972swap_checked fusedMap0972swap_checked
    DegreeOneSmallComparisons.comparison0972
#print axioms sourceMap0972swap_checked
#print axioms fusedMap0972swap_checked
#print axioms certified0972swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
