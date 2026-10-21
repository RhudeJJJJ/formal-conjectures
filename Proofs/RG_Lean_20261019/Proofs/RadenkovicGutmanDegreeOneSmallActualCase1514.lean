/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1514 : Family 9 := level9.get ⟨241,by decide⟩
def sourceMap1514 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,4,2,3] (sourceLabel 9 0 1 v)
def fusedMap1514 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (fusedLabel 9 0 1 v)
theorem sourceMap1514_checked : acceptsGraphIso
    (source (graph core1514) (root 9) 0 1) DegreeOneSmallSpectrum1406.graph sourceMap1514=true := by decide +kernel
theorem fusedMap1514_checked : acceptsGraphIso
    (fused (graph core1514) (root 9) 0 1) DegreeOneSmallSpectrum1454.graph fusedMap1514=true := by decide +kernel
theorem certified1514 : Certified (graph core1514) (root 9) 0 1 :=
  of_native_maps core1514 DegreeOneSmallSpectrum1406.graph DegreeOneSmallSpectrum1454.graph
    sourceMap1514 fusedMap1514 sourceMap1514_checked fusedMap1514_checked
    DegreeOneSmallComparisons.comparison1514
#print axioms sourceMap1514_checked
#print axioms fusedMap1514_checked
#print axioms certified1514
def sourceMap1514swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,2,3,4] (sourceLabel 9 1 0 v)
def fusedMap1514swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (fusedLabel 9 1 0 v)
theorem sourceMap1514swap_checked : acceptsGraphIso
    (source (graph core1514) (root 9) 1 0) DegreeOneSmallSpectrum1406.graph sourceMap1514swap=true := by decide +kernel
theorem fusedMap1514swap_checked : acceptsGraphIso
    (fused (graph core1514) (root 9) 1 0) DegreeOneSmallSpectrum1454.graph fusedMap1514swap=true := by decide +kernel
theorem certified1514swap : Certified (graph core1514) (root 9) 1 0 :=
  of_native_maps core1514 DegreeOneSmallSpectrum1406.graph DegreeOneSmallSpectrum1454.graph
    sourceMap1514swap fusedMap1514swap sourceMap1514swap_checked fusedMap1514swap_checked
    DegreeOneSmallComparisons.comparison1514
#print axioms sourceMap1514swap_checked
#print axioms fusedMap1514swap_checked
#print axioms certified1514swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
