/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1089 : Family 8 := level8.get ⟨144,by decide⟩
def sourceMap1089 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1089 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1089_checked : acceptsGraphIso
    (source (graph core1089) (root 8) 0 2) DegreeOneSmallSpectrum1369.graph sourceMap1089=true := by decide +kernel
theorem fusedMap1089_checked : acceptsGraphIso
    (fused (graph core1089) (root 8) 0 2) DegreeOneSmallSpectrum1370.graph fusedMap1089=true := by decide +kernel
theorem certified1089 : Certified (graph core1089) (root 8) 0 2 :=
  of_native_maps core1089 DegreeOneSmallSpectrum1369.graph DegreeOneSmallSpectrum1370.graph
    sourceMap1089 fusedMap1089 sourceMap1089_checked fusedMap1089_checked
    DegreeOneSmallComparisons.comparison1089
#print axioms sourceMap1089_checked
#print axioms fusedMap1089_checked
#print axioms certified1089
def sourceMap1089swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1089swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1089swap_checked : acceptsGraphIso
    (source (graph core1089) (root 8) 2 0) DegreeOneSmallSpectrum1369.graph sourceMap1089swap=true := by decide +kernel
theorem fusedMap1089swap_checked : acceptsGraphIso
    (fused (graph core1089) (root 8) 2 0) DegreeOneSmallSpectrum1370.graph fusedMap1089swap=true := by decide +kernel
theorem certified1089swap : Certified (graph core1089) (root 8) 2 0 :=
  of_native_maps core1089 DegreeOneSmallSpectrum1369.graph DegreeOneSmallSpectrum1370.graph
    sourceMap1089swap fusedMap1089swap sourceMap1089swap_checked fusedMap1089swap_checked
    DegreeOneSmallComparisons.comparison1089
#print axioms sourceMap1089swap_checked
#print axioms fusedMap1089swap_checked
#print axioms certified1089swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
