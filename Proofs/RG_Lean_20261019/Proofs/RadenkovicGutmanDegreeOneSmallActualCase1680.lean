/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1680 : Family 9 := level9.get ⟨441,by decide⟩
def sourceMap1680 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,10,8,9] (sourceLabel 9 0 1 v)
def fusedMap1680 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1680_checked : acceptsGraphIso
    (source (graph core1680) (root 9) 0 1) DegreeOneSmallSpectrum1940.graph sourceMap1680=true := by decide +kernel
theorem fusedMap1680_checked : acceptsGraphIso
    (fused (graph core1680) (root 9) 0 1) DegreeOneSmallSpectrum1354.graph fusedMap1680=true := by decide +kernel
theorem certified1680 : Certified (graph core1680) (root 9) 0 1 :=
  of_native_maps core1680 DegreeOneSmallSpectrum1940.graph DegreeOneSmallSpectrum1354.graph
    sourceMap1680 fusedMap1680 sourceMap1680_checked fusedMap1680_checked
    DegreeOneSmallComparisons.comparison1680
#print axioms sourceMap1680_checked
#print axioms fusedMap1680_checked
#print axioms certified1680
def sourceMap1680swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 9 1 0 v)
def fusedMap1680swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1680swap_checked : acceptsGraphIso
    (source (graph core1680) (root 9) 1 0) DegreeOneSmallSpectrum1940.graph sourceMap1680swap=true := by decide +kernel
theorem fusedMap1680swap_checked : acceptsGraphIso
    (fused (graph core1680) (root 9) 1 0) DegreeOneSmallSpectrum1354.graph fusedMap1680swap=true := by decide +kernel
theorem certified1680swap : Certified (graph core1680) (root 9) 1 0 :=
  of_native_maps core1680 DegreeOneSmallSpectrum1940.graph DegreeOneSmallSpectrum1354.graph
    sourceMap1680swap fusedMap1680swap sourceMap1680swap_checked fusedMap1680swap_checked
    DegreeOneSmallComparisons.comparison1680
#print axioms sourceMap1680swap_checked
#print axioms fusedMap1680swap_checked
#print axioms certified1680swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
