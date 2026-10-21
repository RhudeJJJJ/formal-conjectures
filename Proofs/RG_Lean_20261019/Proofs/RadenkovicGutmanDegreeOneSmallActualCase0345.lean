/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0345 : Family 6 := level6.get ⟨10,by decide⟩
def sourceMap0345 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 3) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9] (sourceLabel 6 1 2 v)
def fusedMap0345 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 1 2 v)
theorem sourceMap0345_checked : acceptsGraphIso
    (source (graph core0345) (root 6) 1 2) DegreeOneSmallSpectrum515.graph sourceMap0345=true := by decide +kernel
theorem fusedMap0345_checked : acceptsGraphIso
    (fused (graph core0345) (root 6) 1 2) DegreeOneSmallSpectrum379.graph fusedMap0345=true := by decide +kernel
theorem certified0345 : Certified (graph core0345) (root 6) 1 2 :=
  of_native_maps core0345 DegreeOneSmallSpectrum515.graph DegreeOneSmallSpectrum379.graph
    sourceMap0345 fusedMap0345 sourceMap0345_checked fusedMap0345_checked
    DegreeOneSmallComparisons.comparison0345
#print axioms sourceMap0345_checked
#print axioms fusedMap0345_checked
#print axioms certified0345
def sourceMap0345swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11] (sourceLabel 6 2 1 v)
def fusedMap0345swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 2 1 v)
theorem sourceMap0345swap_checked : acceptsGraphIso
    (source (graph core0345) (root 6) 2 1) DegreeOneSmallSpectrum515.graph sourceMap0345swap=true := by decide +kernel
theorem fusedMap0345swap_checked : acceptsGraphIso
    (fused (graph core0345) (root 6) 2 1) DegreeOneSmallSpectrum379.graph fusedMap0345swap=true := by decide +kernel
theorem certified0345swap : Certified (graph core0345) (root 6) 2 1 :=
  of_native_maps core0345 DegreeOneSmallSpectrum515.graph DegreeOneSmallSpectrum379.graph
    sourceMap0345swap fusedMap0345swap sourceMap0345swap_checked fusedMap0345swap_checked
    DegreeOneSmallComparisons.comparison0345
#print axioms sourceMap0345swap_checked
#print axioms fusedMap0345swap_checked
#print axioms certified0345swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
