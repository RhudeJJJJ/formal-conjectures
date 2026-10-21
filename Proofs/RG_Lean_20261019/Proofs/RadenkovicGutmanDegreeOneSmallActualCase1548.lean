/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1548 : Family 9 := level9.get ⟨276,by decide⟩
def sourceMap1548 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,4,2,3] (sourceLabel 9 0 1 v)
def fusedMap1548 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (fusedLabel 9 0 1 v)
theorem sourceMap1548_checked : acceptsGraphIso
    (source (graph core1548) (root 9) 0 1) DegreeOneSmallSpectrum1402.graph sourceMap1548=true := by decide +kernel
theorem fusedMap1548_checked : acceptsGraphIso
    (fused (graph core1548) (root 9) 0 1) DegreeOneSmallSpectrum1505.graph fusedMap1548=true := by decide +kernel
theorem certified1548 : Certified (graph core1548) (root 9) 0 1 :=
  of_native_maps core1548 DegreeOneSmallSpectrum1402.graph DegreeOneSmallSpectrum1505.graph
    sourceMap1548 fusedMap1548 sourceMap1548_checked fusedMap1548_checked
    DegreeOneSmallComparisons.comparison1548
#print axioms sourceMap1548_checked
#print axioms fusedMap1548_checked
#print axioms certified1548
def sourceMap1548swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,2,3,4] (sourceLabel 9 1 0 v)
def fusedMap1548swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (fusedLabel 9 1 0 v)
theorem sourceMap1548swap_checked : acceptsGraphIso
    (source (graph core1548) (root 9) 1 0) DegreeOneSmallSpectrum1402.graph sourceMap1548swap=true := by decide +kernel
theorem fusedMap1548swap_checked : acceptsGraphIso
    (fused (graph core1548) (root 9) 1 0) DegreeOneSmallSpectrum1505.graph fusedMap1548swap=true := by decide +kernel
theorem certified1548swap : Certified (graph core1548) (root 9) 1 0 :=
  of_native_maps core1548 DegreeOneSmallSpectrum1402.graph DegreeOneSmallSpectrum1505.graph
    sourceMap1548swap fusedMap1548swap sourceMap1548swap_checked fusedMap1548swap_checked
    DegreeOneSmallComparisons.comparison1548
#print axioms sourceMap1548swap_checked
#print axioms fusedMap1548swap_checked
#print axioms certified1548swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
