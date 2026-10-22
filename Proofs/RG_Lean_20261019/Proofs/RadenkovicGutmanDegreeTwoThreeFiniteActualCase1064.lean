/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1064 : Family 7 := level7.get ⟨24,by decide⟩
def sourceMap1064 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,5,6,7,2,3,4] (sourceLabel 7 0 2 v)
def fusedMap1064 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,7,8,9,10,11,5,6,1,2,3,4] (fusedLabel 7 0 2 v)
theorem sourceMap1064_checked : acceptsGraphIso
    (source (graph core1064) (root 7) 0 2) DegreeOneSmallSpectrum571.graph sourceMap1064=true := by decide +kernel
theorem fusedMap1064_checked : acceptsGraphIso
    (fused (graph core1064) (root 7) 0 2) DegreeOneSmallSpectrum393.graph fusedMap1064=true := by decide +kernel
theorem certified1064 : Certified (graph core1064) (root 7) 0 2 :=
  of_native_maps core1064 DegreeOneSmallSpectrum571.graph DegreeOneSmallSpectrum393.graph
    sourceMap1064 fusedMap1064 sourceMap1064_checked fusedMap1064_checked
    DegreeTwoThreeFiniteComparisons.comparison1064
#print axioms sourceMap1064_checked
#print axioms fusedMap1064_checked
#print axioms certified1064
def sourceMap1064swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,5,6,2,3,4,7] (sourceLabel 7 2 0 v)
def fusedMap1064swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,7,8,9,10,11,5,6,1,2,3,4] (fusedLabel 7 2 0 v)
theorem sourceMap1064swap_checked : acceptsGraphIso
    (source (graph core1064) (root 7) 2 0) DegreeOneSmallSpectrum571.graph sourceMap1064swap=true := by decide +kernel
theorem fusedMap1064swap_checked : acceptsGraphIso
    (fused (graph core1064) (root 7) 2 0) DegreeOneSmallSpectrum393.graph fusedMap1064swap=true := by decide +kernel
theorem certified1064swap : Certified (graph core1064) (root 7) 2 0 :=
  of_native_maps core1064 DegreeOneSmallSpectrum571.graph DegreeOneSmallSpectrum393.graph
    sourceMap1064swap fusedMap1064swap sourceMap1064swap_checked fusedMap1064swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1064
#print axioms sourceMap1064swap_checked
#print axioms fusedMap1064swap_checked
#print axioms certified1064swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
