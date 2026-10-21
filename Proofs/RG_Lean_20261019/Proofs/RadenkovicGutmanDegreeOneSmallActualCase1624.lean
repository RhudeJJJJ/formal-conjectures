/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1624 : Family 9 := level9.get ⟨366,by decide⟩
def sourceMap1624 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1624 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1624_checked : acceptsGraphIso
    (source (graph core1624) (root 9) 0 1) DegreeOneSmallSpectrum1782.graph sourceMap1624=true := by decide +kernel
theorem fusedMap1624_checked : acceptsGraphIso
    (fused (graph core1624) (root 9) 0 1) DegreeOneSmallSpectrum1113.graph fusedMap1624=true := by decide +kernel
theorem certified1624 : Certified (graph core1624) (root 9) 0 1 :=
  of_native_maps core1624 DegreeOneSmallSpectrum1782.graph DegreeOneSmallSpectrum1113.graph
    sourceMap1624 fusedMap1624 sourceMap1624_checked fusedMap1624_checked
    DegreeOneSmallComparisons.comparison1624
#print axioms sourceMap1624_checked
#print axioms fusedMap1624_checked
#print axioms certified1624
def sourceMap1624swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1624swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1624swap_checked : acceptsGraphIso
    (source (graph core1624) (root 9) 1 0) DegreeOneSmallSpectrum1782.graph sourceMap1624swap=true := by decide +kernel
theorem fusedMap1624swap_checked : acceptsGraphIso
    (fused (graph core1624) (root 9) 1 0) DegreeOneSmallSpectrum1113.graph fusedMap1624swap=true := by decide +kernel
theorem certified1624swap : Certified (graph core1624) (root 9) 1 0 :=
  of_native_maps core1624 DegreeOneSmallSpectrum1782.graph DegreeOneSmallSpectrum1113.graph
    sourceMap1624swap fusedMap1624swap sourceMap1624swap_checked fusedMap1624swap_checked
    DegreeOneSmallComparisons.comparison1624
#print axioms sourceMap1624swap_checked
#print axioms fusedMap1624swap_checked
#print axioms certified1624swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
