/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1530 : Family 9 := level9.get ⟨259,by decide⟩
def sourceMap1530 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,4,2,3] (sourceLabel 9 0 1 v)
def fusedMap1530 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1530_checked : acceptsGraphIso
    (source (graph core1530) (root 9) 0 1) DegreeOneSmallSpectrum1444.graph sourceMap1530=true := by decide +kernel
theorem fusedMap1530_checked : acceptsGraphIso
    (fused (graph core1530) (root 9) 0 1) DegreeOneSmallSpectrum1481.graph fusedMap1530=true := by decide +kernel
theorem certified1530 : Certified (graph core1530) (root 9) 0 1 :=
  of_native_maps core1530 DegreeOneSmallSpectrum1444.graph DegreeOneSmallSpectrum1481.graph
    sourceMap1530 fusedMap1530 sourceMap1530_checked fusedMap1530_checked
    DegreeOneSmallComparisons.comparison1530
#print axioms sourceMap1530_checked
#print axioms fusedMap1530_checked
#print axioms certified1530
def sourceMap1530swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (sourceLabel 9 1 0 v)
def fusedMap1530swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1530swap_checked : acceptsGraphIso
    (source (graph core1530) (root 9) 1 0) DegreeOneSmallSpectrum1444.graph sourceMap1530swap=true := by decide +kernel
theorem fusedMap1530swap_checked : acceptsGraphIso
    (fused (graph core1530) (root 9) 1 0) DegreeOneSmallSpectrum1481.graph fusedMap1530swap=true := by decide +kernel
theorem certified1530swap : Certified (graph core1530) (root 9) 1 0 :=
  of_native_maps core1530 DegreeOneSmallSpectrum1444.graph DegreeOneSmallSpectrum1481.graph
    sourceMap1530swap fusedMap1530swap sourceMap1530swap_checked fusedMap1530swap_checked
    DegreeOneSmallComparisons.comparison1530
#print axioms sourceMap1530swap_checked
#print axioms fusedMap1530swap_checked
#print axioms certified1530swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
