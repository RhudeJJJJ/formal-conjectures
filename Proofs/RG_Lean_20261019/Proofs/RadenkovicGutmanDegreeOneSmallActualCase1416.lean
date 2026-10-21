/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1416 : Family 9 := level9.get ⟨158,by decide⟩
def sourceMap1416 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1416 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1416_checked : acceptsGraphIso
    (source (graph core1416) (root 9) 0 1) DegreeOneSmallSpectrum1099.graph sourceMap1416=true := by decide +kernel
theorem fusedMap1416_checked : acceptsGraphIso
    (fused (graph core1416) (root 9) 0 1) DegreeOneSmallSpectrum1101.graph fusedMap1416=true := by decide +kernel
theorem certified1416 : Certified (graph core1416) (root 9) 0 1 :=
  of_native_maps core1416 DegreeOneSmallSpectrum1099.graph DegreeOneSmallSpectrum1101.graph
    sourceMap1416 fusedMap1416 sourceMap1416_checked fusedMap1416_checked
    DegreeOneSmallComparisons.comparison1416
#print axioms sourceMap1416_checked
#print axioms fusedMap1416_checked
#print axioms certified1416
def sourceMap1416swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1416swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1416swap_checked : acceptsGraphIso
    (source (graph core1416) (root 9) 1 0) DegreeOneSmallSpectrum1099.graph sourceMap1416swap=true := by decide +kernel
theorem fusedMap1416swap_checked : acceptsGraphIso
    (fused (graph core1416) (root 9) 1 0) DegreeOneSmallSpectrum1101.graph fusedMap1416swap=true := by decide +kernel
theorem certified1416swap : Certified (graph core1416) (root 9) 1 0 :=
  of_native_maps core1416 DegreeOneSmallSpectrum1099.graph DegreeOneSmallSpectrum1101.graph
    sourceMap1416swap fusedMap1416swap sourceMap1416swap_checked fusedMap1416swap_checked
    DegreeOneSmallComparisons.comparison1416
#print axioms sourceMap1416swap_checked
#print axioms fusedMap1416swap_checked
#print axioms certified1416swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
