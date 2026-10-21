/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1618 : Family 9 := level9.get ⟨359,by decide⟩
def sourceMap1618 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,11,9,10] (sourceLabel 9 0 1 v)
def fusedMap1618 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1618_checked : acceptsGraphIso
    (source (graph core1618) (root 9) 0 1) DegreeOneSmallSpectrum1752.graph sourceMap1618=true := by decide +kernel
theorem fusedMap1618_checked : acceptsGraphIso
    (fused (graph core1618) (root 9) 0 1) DegreeOneSmallSpectrum1091.graph fusedMap1618=true := by decide +kernel
theorem certified1618 : Certified (graph core1618) (root 9) 0 1 :=
  of_native_maps core1618 DegreeOneSmallSpectrum1752.graph DegreeOneSmallSpectrum1091.graph
    sourceMap1618 fusedMap1618 sourceMap1618_checked fusedMap1618_checked
    DegreeOneSmallComparisons.comparison1618
#print axioms sourceMap1618_checked
#print axioms fusedMap1618_checked
#print axioms certified1618
def sourceMap1618swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 9 1 0 v)
def fusedMap1618swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1618swap_checked : acceptsGraphIso
    (source (graph core1618) (root 9) 1 0) DegreeOneSmallSpectrum1752.graph sourceMap1618swap=true := by decide +kernel
theorem fusedMap1618swap_checked : acceptsGraphIso
    (fused (graph core1618) (root 9) 1 0) DegreeOneSmallSpectrum1091.graph fusedMap1618swap=true := by decide +kernel
theorem certified1618swap : Certified (graph core1618) (root 9) 1 0 :=
  of_native_maps core1618 DegreeOneSmallSpectrum1752.graph DegreeOneSmallSpectrum1091.graph
    sourceMap1618swap fusedMap1618swap sourceMap1618swap_checked fusedMap1618swap_checked
    DegreeOneSmallComparisons.comparison1618
#print axioms sourceMap1618swap_checked
#print axioms fusedMap1618swap_checked
#print axioms certified1618swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
