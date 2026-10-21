/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0156 : Family 4 := level4.get ⟨4,by decide⟩
def sourceMap0156 : (Vertices 4 ⊕ Fin 3 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,4,5,6,7,1,2,3,8,9,10,11] (sourceLabel 4 2 3 v)
def fusedMap0156 : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11] (fusedLabel 4 2 3 v)
theorem sourceMap0156_checked : acceptsGraphIso
    (source (graph core0156) (root 4) 2 3) DegreeOneSmallSpectrum564.graph sourceMap0156=true := by decide +kernel
theorem fusedMap0156_checked : acceptsGraphIso
    (fused (graph core0156) (root 4) 2 3) DegreeOneSmallSpectrum370.graph fusedMap0156=true := by decide +kernel
theorem certified0156 : Certified (graph core0156) (root 4) 2 3 :=
  of_native_maps core0156 DegreeOneSmallSpectrum564.graph DegreeOneSmallSpectrum370.graph
    sourceMap0156 fusedMap0156 sourceMap0156_checked fusedMap0156_checked
    DegreeOneSmallComparisons.comparison0156
#print axioms sourceMap0156_checked
#print axioms fusedMap0156_checked
#print axioms certified0156
def sourceMap0156swap : (Vertices 4 ⊕ Fin 4 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,4,5,6,7,8,9,10,11,1,2,3] (sourceLabel 4 3 2 v)
def fusedMap0156swap : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11] (fusedLabel 4 3 2 v)
theorem sourceMap0156swap_checked : acceptsGraphIso
    (source (graph core0156) (root 4) 3 2) DegreeOneSmallSpectrum564.graph sourceMap0156swap=true := by decide +kernel
theorem fusedMap0156swap_checked : acceptsGraphIso
    (fused (graph core0156) (root 4) 3 2) DegreeOneSmallSpectrum370.graph fusedMap0156swap=true := by decide +kernel
theorem certified0156swap : Certified (graph core0156) (root 4) 3 2 :=
  of_native_maps core0156 DegreeOneSmallSpectrum564.graph DegreeOneSmallSpectrum370.graph
    sourceMap0156swap fusedMap0156swap sourceMap0156swap_checked fusedMap0156swap_checked
    DegreeOneSmallComparisons.comparison0156
#print axioms sourceMap0156swap_checked
#print axioms fusedMap0156swap_checked
#print axioms certified0156swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
