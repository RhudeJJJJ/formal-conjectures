/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1754 : Family 9 := level9.get ⟨592,by decide⟩
def sourceMap1754 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1754 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1754_checked : acceptsGraphIso
    (source (graph core1754) (root 9) 0 1) DegreeOneSmallSpectrum1736.graph sourceMap1754=true := by decide +kernel
theorem fusedMap1754_checked : acceptsGraphIso
    (fused (graph core1754) (root 9) 0 1) DegreeOneSmallSpectrum1737.graph fusedMap1754=true := by decide +kernel
theorem certified1754 : Certified (graph core1754) (root 9) 0 1 :=
  of_native_maps core1754 DegreeOneSmallSpectrum1736.graph DegreeOneSmallSpectrum1737.graph
    sourceMap1754 fusedMap1754 sourceMap1754_checked fusedMap1754_checked
    DegreeOneSmallComparisons.comparison1754
#print axioms sourceMap1754_checked
#print axioms fusedMap1754_checked
#print axioms certified1754
def sourceMap1754swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1754swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1754swap_checked : acceptsGraphIso
    (source (graph core1754) (root 9) 1 0) DegreeOneSmallSpectrum1736.graph sourceMap1754swap=true := by decide +kernel
theorem fusedMap1754swap_checked : acceptsGraphIso
    (fused (graph core1754) (root 9) 1 0) DegreeOneSmallSpectrum1737.graph fusedMap1754swap=true := by decide +kernel
theorem certified1754swap : Certified (graph core1754) (root 9) 1 0 :=
  of_native_maps core1754 DegreeOneSmallSpectrum1736.graph DegreeOneSmallSpectrum1737.graph
    sourceMap1754swap fusedMap1754swap sourceMap1754swap_checked fusedMap1754swap_checked
    DegreeOneSmallComparisons.comparison1754
#print axioms sourceMap1754swap_checked
#print axioms fusedMap1754swap_checked
#print axioms certified1754swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
