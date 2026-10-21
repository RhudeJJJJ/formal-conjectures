/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1526 : Family 9 := level9.get ⟨256,by decide⟩
def sourceMap1526 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,5,4,2,3] (sourceLabel 9 0 1 v)
def fusedMap1526 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (fusedLabel 9 0 1 v)
theorem sourceMap1526_checked : acceptsGraphIso
    (source (graph core1526) (root 9) 0 1) DegreeOneSmallSpectrum1428.graph sourceMap1526=true := by decide +kernel
theorem fusedMap1526_checked : acceptsGraphIso
    (fused (graph core1526) (root 9) 0 1) DegreeOneSmallSpectrum1475.graph fusedMap1526=true := by decide +kernel
theorem certified1526 : Certified (graph core1526) (root 9) 0 1 :=
  of_native_maps core1526 DegreeOneSmallSpectrum1428.graph DegreeOneSmallSpectrum1475.graph
    sourceMap1526 fusedMap1526 sourceMap1526_checked fusedMap1526_checked
    DegreeOneSmallComparisons.comparison1526
#print axioms sourceMap1526_checked
#print axioms fusedMap1526_checked
#print axioms certified1526
def sourceMap1526swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,5,2,3,4] (sourceLabel 9 1 0 v)
def fusedMap1526swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (fusedLabel 9 1 0 v)
theorem sourceMap1526swap_checked : acceptsGraphIso
    (source (graph core1526) (root 9) 1 0) DegreeOneSmallSpectrum1428.graph sourceMap1526swap=true := by decide +kernel
theorem fusedMap1526swap_checked : acceptsGraphIso
    (fused (graph core1526) (root 9) 1 0) DegreeOneSmallSpectrum1475.graph fusedMap1526swap=true := by decide +kernel
theorem certified1526swap : Certified (graph core1526) (root 9) 1 0 :=
  of_native_maps core1526 DegreeOneSmallSpectrum1428.graph DegreeOneSmallSpectrum1475.graph
    sourceMap1526swap fusedMap1526swap sourceMap1526swap_checked fusedMap1526swap_checked
    DegreeOneSmallComparisons.comparison1526
#print axioms sourceMap1526swap_checked
#print axioms fusedMap1526swap_checked
#print axioms certified1526swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
