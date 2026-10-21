/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1696 : Family 9 := level9.get ⟨461,by decide⟩
def sourceMap1696 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,4,2,3] (sourceLabel 9 0 1 v)
def fusedMap1696 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1696_checked : acceptsGraphIso
    (source (graph core1696) (root 9) 0 1) DegreeOneSmallSpectrum1958.graph sourceMap1696=true := by decide +kernel
theorem fusedMap1696_checked : acceptsGraphIso
    (fused (graph core1696) (root 9) 0 1) DegreeOneSmallSpectrum1399.graph fusedMap1696=true := by decide +kernel
theorem certified1696 : Certified (graph core1696) (root 9) 0 1 :=
  of_native_maps core1696 DegreeOneSmallSpectrum1958.graph DegreeOneSmallSpectrum1399.graph
    sourceMap1696 fusedMap1696 sourceMap1696_checked fusedMap1696_checked
    DegreeOneSmallComparisons.comparison1696
#print axioms sourceMap1696_checked
#print axioms fusedMap1696_checked
#print axioms certified1696
def sourceMap1696swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (sourceLabel 9 1 0 v)
def fusedMap1696swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1696swap_checked : acceptsGraphIso
    (source (graph core1696) (root 9) 1 0) DegreeOneSmallSpectrum1958.graph sourceMap1696swap=true := by decide +kernel
theorem fusedMap1696swap_checked : acceptsGraphIso
    (fused (graph core1696) (root 9) 1 0) DegreeOneSmallSpectrum1399.graph fusedMap1696swap=true := by decide +kernel
theorem certified1696swap : Certified (graph core1696) (root 9) 1 0 :=
  of_native_maps core1696 DegreeOneSmallSpectrum1958.graph DegreeOneSmallSpectrum1399.graph
    sourceMap1696swap fusedMap1696swap sourceMap1696swap_checked fusedMap1696swap_checked
    DegreeOneSmallComparisons.comparison1696
#print axioms sourceMap1696swap_checked
#print axioms fusedMap1696swap_checked
#print axioms certified1696swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
