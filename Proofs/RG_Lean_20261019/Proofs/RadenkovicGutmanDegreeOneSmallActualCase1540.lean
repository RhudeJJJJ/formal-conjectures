/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1540 : Family 9 := level9.get ⟨268,by decide⟩
def sourceMap1540 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,5,4,2,3] (sourceLabel 9 0 1 v)
def fusedMap1540 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (fusedLabel 9 0 1 v)
theorem sourceMap1540_checked : acceptsGraphIso
    (source (graph core1540) (root 9) 0 1) DegreeOneSmallSpectrum1431.graph sourceMap1540=true := by decide +kernel
theorem fusedMap1540_checked : acceptsGraphIso
    (fused (graph core1540) (root 9) 0 1) DegreeOneSmallSpectrum1497.graph fusedMap1540=true := by decide +kernel
theorem certified1540 : Certified (graph core1540) (root 9) 0 1 :=
  of_native_maps core1540 DegreeOneSmallSpectrum1431.graph DegreeOneSmallSpectrum1497.graph
    sourceMap1540 fusedMap1540 sourceMap1540_checked fusedMap1540_checked
    DegreeOneSmallComparisons.comparison1540
#print axioms sourceMap1540_checked
#print axioms fusedMap1540_checked
#print axioms certified1540
def sourceMap1540swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,5,2,3,4] (sourceLabel 9 1 0 v)
def fusedMap1540swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (fusedLabel 9 1 0 v)
theorem sourceMap1540swap_checked : acceptsGraphIso
    (source (graph core1540) (root 9) 1 0) DegreeOneSmallSpectrum1431.graph sourceMap1540swap=true := by decide +kernel
theorem fusedMap1540swap_checked : acceptsGraphIso
    (fused (graph core1540) (root 9) 1 0) DegreeOneSmallSpectrum1497.graph fusedMap1540swap=true := by decide +kernel
theorem certified1540swap : Certified (graph core1540) (root 9) 1 0 :=
  of_native_maps core1540 DegreeOneSmallSpectrum1431.graph DegreeOneSmallSpectrum1497.graph
    sourceMap1540swap fusedMap1540swap sourceMap1540swap_checked fusedMap1540swap_checked
    DegreeOneSmallComparisons.comparison1540
#print axioms sourceMap1540swap_checked
#print axioms fusedMap1540swap_checked
#print axioms certified1540swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
