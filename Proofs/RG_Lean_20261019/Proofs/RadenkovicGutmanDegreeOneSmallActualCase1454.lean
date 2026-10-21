/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1454 : Family 9 := level9.get ⟨188,by decide⟩
def sourceMap1454 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,5,0,1,2,3,4,10,11,12,9,7,8] (sourceLabel 9 0 1 v)
def fusedMap1454 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (fusedLabel 9 0 1 v)
theorem sourceMap1454_checked : acceptsGraphIso
    (source (graph core1454) (root 9) 0 1) DegreeOneSmallSpectrum1266.graph sourceMap1454=true := by decide +kernel
theorem fusedMap1454_checked : acceptsGraphIso
    (fused (graph core1454) (root 9) 0 1) DegreeOneSmallSpectrum1289.graph fusedMap1454=true := by decide +kernel
theorem certified1454 : Certified (graph core1454) (root 9) 0 1 :=
  of_native_maps core1454 DegreeOneSmallSpectrum1266.graph DegreeOneSmallSpectrum1289.graph
    sourceMap1454 fusedMap1454 sourceMap1454_checked fusedMap1454_checked
    DegreeOneSmallComparisons.comparison1454
#print axioms sourceMap1454_checked
#print axioms fusedMap1454_checked
#print axioms certified1454
def sourceMap1454swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,5,0,1,2,3,4,10,11,12,7,8,9] (sourceLabel 9 1 0 v)
def fusedMap1454swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (fusedLabel 9 1 0 v)
theorem sourceMap1454swap_checked : acceptsGraphIso
    (source (graph core1454) (root 9) 1 0) DegreeOneSmallSpectrum1266.graph sourceMap1454swap=true := by decide +kernel
theorem fusedMap1454swap_checked : acceptsGraphIso
    (fused (graph core1454) (root 9) 1 0) DegreeOneSmallSpectrum1289.graph fusedMap1454swap=true := by decide +kernel
theorem certified1454swap : Certified (graph core1454) (root 9) 1 0 :=
  of_native_maps core1454 DegreeOneSmallSpectrum1266.graph DegreeOneSmallSpectrum1289.graph
    sourceMap1454swap fusedMap1454swap sourceMap1454swap_checked fusedMap1454swap_checked
    DegreeOneSmallComparisons.comparison1454
#print axioms sourceMap1454swap_checked
#print axioms fusedMap1454swap_checked
#print axioms certified1454swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
