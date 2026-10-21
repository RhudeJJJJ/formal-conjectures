/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1452 : Family 9 := level9.get ⟨187,by decide⟩
def sourceMap1452 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,5,0,1,2,3,4,10,11,12,9,7,8] (sourceLabel 9 0 1 v)
def fusedMap1452 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (fusedLabel 9 0 1 v)
theorem sourceMap1452_checked : acceptsGraphIso
    (source (graph core1452) (root 9) 0 1) DegreeOneSmallSpectrum1265.graph sourceMap1452=true := by decide +kernel
theorem fusedMap1452_checked : acceptsGraphIso
    (fused (graph core1452) (root 9) 0 1) DegreeOneSmallSpectrum1288.graph fusedMap1452=true := by decide +kernel
theorem certified1452 : Certified (graph core1452) (root 9) 0 1 :=
  of_native_maps core1452 DegreeOneSmallSpectrum1265.graph DegreeOneSmallSpectrum1288.graph
    sourceMap1452 fusedMap1452 sourceMap1452_checked fusedMap1452_checked
    DegreeOneSmallComparisons.comparison1452
#print axioms sourceMap1452_checked
#print axioms fusedMap1452_checked
#print axioms certified1452
def sourceMap1452swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,5,0,1,2,3,4,10,11,12,7,8,9] (sourceLabel 9 1 0 v)
def fusedMap1452swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (fusedLabel 9 1 0 v)
theorem sourceMap1452swap_checked : acceptsGraphIso
    (source (graph core1452) (root 9) 1 0) DegreeOneSmallSpectrum1265.graph sourceMap1452swap=true := by decide +kernel
theorem fusedMap1452swap_checked : acceptsGraphIso
    (fused (graph core1452) (root 9) 1 0) DegreeOneSmallSpectrum1288.graph fusedMap1452swap=true := by decide +kernel
theorem certified1452swap : Certified (graph core1452) (root 9) 1 0 :=
  of_native_maps core1452 DegreeOneSmallSpectrum1265.graph DegreeOneSmallSpectrum1288.graph
    sourceMap1452swap fusedMap1452swap sourceMap1452swap_checked fusedMap1452swap_checked
    DegreeOneSmallComparisons.comparison1452
#print axioms sourceMap1452swap_checked
#print axioms fusedMap1452swap_checked
#print axioms certified1452swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
