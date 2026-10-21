/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1436 : Family 9 := level9.get ⟨174,by decide⟩
def sourceMap1436 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1436 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1436_checked : acceptsGraphIso
    (source (graph core1436) (root 9) 0 1) DegreeOneSmallSpectrum1187.graph sourceMap1436=true := by decide +kernel
theorem fusedMap1436_checked : acceptsGraphIso
    (fused (graph core1436) (root 9) 0 1) DegreeOneSmallSpectrum1189.graph fusedMap1436=true := by decide +kernel
theorem certified1436 : Certified (graph core1436) (root 9) 0 1 :=
  of_native_maps core1436 DegreeOneSmallSpectrum1187.graph DegreeOneSmallSpectrum1189.graph
    sourceMap1436 fusedMap1436 sourceMap1436_checked fusedMap1436_checked
    DegreeOneSmallComparisons.comparison1436
#print axioms sourceMap1436_checked
#print axioms fusedMap1436_checked
#print axioms certified1436
def sourceMap1436swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1436swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1436swap_checked : acceptsGraphIso
    (source (graph core1436) (root 9) 1 0) DegreeOneSmallSpectrum1187.graph sourceMap1436swap=true := by decide +kernel
theorem fusedMap1436swap_checked : acceptsGraphIso
    (fused (graph core1436) (root 9) 1 0) DegreeOneSmallSpectrum1189.graph fusedMap1436swap=true := by decide +kernel
theorem certified1436swap : Certified (graph core1436) (root 9) 1 0 :=
  of_native_maps core1436 DegreeOneSmallSpectrum1187.graph DegreeOneSmallSpectrum1189.graph
    sourceMap1436swap fusedMap1436swap sourceMap1436swap_checked fusedMap1436swap_checked
    DegreeOneSmallComparisons.comparison1436
#print axioms sourceMap1436swap_checked
#print axioms fusedMap1436swap_checked
#print axioms certified1436swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
