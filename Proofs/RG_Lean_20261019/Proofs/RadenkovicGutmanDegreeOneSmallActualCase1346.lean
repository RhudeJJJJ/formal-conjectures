/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1346 : Family 9 := level9.get ⟨99,by decide⟩
def sourceMap1346 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 9 0 1 v)
def fusedMap1346 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1346_checked : acceptsGraphIso
    (source (graph core1346) (root 9) 0 1) DegreeOneSmallSpectrum1448.graph sourceMap1346=true := by decide +kernel
theorem fusedMap1346_checked : acceptsGraphIso
    (fused (graph core1346) (root 9) 0 1) DegreeOneSmallSpectrum952.graph fusedMap1346=true := by decide +kernel
theorem certified1346 : Certified (graph core1346) (root 9) 0 1 :=
  of_native_maps core1346 DegreeOneSmallSpectrum1448.graph DegreeOneSmallSpectrum952.graph
    sourceMap1346 fusedMap1346 sourceMap1346_checked fusedMap1346_checked
    DegreeOneSmallComparisons.comparison1346
#print axioms sourceMap1346_checked
#print axioms fusedMap1346_checked
#print axioms certified1346
def sourceMap1346swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 9 1 0 v)
def fusedMap1346swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1346swap_checked : acceptsGraphIso
    (source (graph core1346) (root 9) 1 0) DegreeOneSmallSpectrum1448.graph sourceMap1346swap=true := by decide +kernel
theorem fusedMap1346swap_checked : acceptsGraphIso
    (fused (graph core1346) (root 9) 1 0) DegreeOneSmallSpectrum952.graph fusedMap1346swap=true := by decide +kernel
theorem certified1346swap : Certified (graph core1346) (root 9) 1 0 :=
  of_native_maps core1346 DegreeOneSmallSpectrum1448.graph DegreeOneSmallSpectrum952.graph
    sourceMap1346swap fusedMap1346swap sourceMap1346swap_checked fusedMap1346swap_checked
    DegreeOneSmallComparisons.comparison1346
#print axioms sourceMap1346swap_checked
#print axioms fusedMap1346swap_checked
#print axioms certified1346swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
