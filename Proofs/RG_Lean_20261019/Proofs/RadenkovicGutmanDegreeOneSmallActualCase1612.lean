/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1612 : Family 9 := level9.get ⟨355,by decide⟩
def sourceMap1612 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,11,9,10] (sourceLabel 9 0 1 v)
def fusedMap1612 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1612_checked : acceptsGraphIso
    (source (graph core1612) (root 9) 0 1) DegreeOneSmallSpectrum1720.graph sourceMap1612=true := by decide +kernel
theorem fusedMap1612_checked : acceptsGraphIso
    (fused (graph core1612) (root 9) 0 1) DegreeOneSmallSpectrum1084.graph fusedMap1612=true := by decide +kernel
theorem certified1612 : Certified (graph core1612) (root 9) 0 1 :=
  of_native_maps core1612 DegreeOneSmallSpectrum1720.graph DegreeOneSmallSpectrum1084.graph
    sourceMap1612 fusedMap1612 sourceMap1612_checked fusedMap1612_checked
    DegreeOneSmallComparisons.comparison1612
#print axioms sourceMap1612_checked
#print axioms fusedMap1612_checked
#print axioms certified1612
def sourceMap1612swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 9 1 0 v)
def fusedMap1612swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1612swap_checked : acceptsGraphIso
    (source (graph core1612) (root 9) 1 0) DegreeOneSmallSpectrum1720.graph sourceMap1612swap=true := by decide +kernel
theorem fusedMap1612swap_checked : acceptsGraphIso
    (fused (graph core1612) (root 9) 1 0) DegreeOneSmallSpectrum1084.graph fusedMap1612swap=true := by decide +kernel
theorem certified1612swap : Certified (graph core1612) (root 9) 1 0 :=
  of_native_maps core1612 DegreeOneSmallSpectrum1720.graph DegreeOneSmallSpectrum1084.graph
    sourceMap1612swap fusedMap1612swap sourceMap1612swap_checked fusedMap1612swap_checked
    DegreeOneSmallComparisons.comparison1612
#print axioms sourceMap1612swap_checked
#print axioms fusedMap1612swap_checked
#print axioms certified1612swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
