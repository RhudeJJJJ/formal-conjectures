/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1116 : Family 8 := level8.get ⟨81,by decide⟩
def sourceMap1116 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,2,3,4] (sourceLabel 8 0 2 v)
def fusedMap1116 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,11,12,7,8,9,10] (fusedLabel 8 0 2 v)
theorem sourceMap1116_checked : acceptsGraphIso
    (source (graph core1116) (root 8) 0 2) DegreeOneSmallSpectrum1484.graph sourceMap1116=true := by decide +kernel
theorem fusedMap1116_checked : acceptsGraphIso
    (fused (graph core1116) (root 8) 0 2) DegreeOneSmallSpectrum963.graph fusedMap1116=true := by decide +kernel
theorem certified1116 : Certified (graph core1116) (root 8) 0 2 :=
  of_native_maps core1116 DegreeOneSmallSpectrum1484.graph DegreeOneSmallSpectrum963.graph
    sourceMap1116 fusedMap1116 sourceMap1116_checked fusedMap1116_checked
    DegreeTwoThreeFiniteComparisons.comparison1116
#print axioms sourceMap1116_checked
#print axioms fusedMap1116_checked
#print axioms certified1116
def sourceMap1116swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,2,3,4,7] (sourceLabel 8 2 0 v)
def fusedMap1116swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,11,12,7,8,9,10] (fusedLabel 8 2 0 v)
theorem sourceMap1116swap_checked : acceptsGraphIso
    (source (graph core1116) (root 8) 2 0) DegreeOneSmallSpectrum1484.graph sourceMap1116swap=true := by decide +kernel
theorem fusedMap1116swap_checked : acceptsGraphIso
    (fused (graph core1116) (root 8) 2 0) DegreeOneSmallSpectrum963.graph fusedMap1116swap=true := by decide +kernel
theorem certified1116swap : Certified (graph core1116) (root 8) 2 0 :=
  of_native_maps core1116 DegreeOneSmallSpectrum1484.graph DegreeOneSmallSpectrum963.graph
    sourceMap1116swap fusedMap1116swap sourceMap1116swap_checked fusedMap1116swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1116
#print axioms sourceMap1116swap_checked
#print axioms fusedMap1116swap_checked
#print axioms certified1116swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
