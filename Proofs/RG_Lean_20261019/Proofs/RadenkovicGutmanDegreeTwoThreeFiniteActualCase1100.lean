/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1100 : Family 8 := level8.get ⟨28,by decide⟩
def sourceMap1100 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,6,2,3,4] (sourceLabel 8 0 2 v)
def fusedMap1100 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,6,2,3,4,5] (fusedLabel 8 0 2 v)
theorem sourceMap1100_checked : acceptsGraphIso
    (source (graph core1100) (root 8) 0 2) DegreeOneSmallSpectrum955.graph sourceMap1100=true := by decide +kernel
theorem fusedMap1100_checked : acceptsGraphIso
    (fused (graph core1100) (root 8) 0 2) DegreeOneSmallSpectrum975.graph fusedMap1100=true := by decide +kernel
theorem certified1100 : Certified (graph core1100) (root 8) 0 2 :=
  of_native_maps core1100 DegreeOneSmallSpectrum955.graph DegreeOneSmallSpectrum975.graph
    sourceMap1100 fusedMap1100 sourceMap1100_checked fusedMap1100_checked
    DegreeTwoThreeFiniteComparisons.comparison1100
#print axioms sourceMap1100_checked
#print axioms fusedMap1100_checked
#print axioms certified1100
def sourceMap1100swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,2,3,4,6] (sourceLabel 8 2 0 v)
def fusedMap1100swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,6,2,3,4,5] (fusedLabel 8 2 0 v)
theorem sourceMap1100swap_checked : acceptsGraphIso
    (source (graph core1100) (root 8) 2 0) DegreeOneSmallSpectrum955.graph sourceMap1100swap=true := by decide +kernel
theorem fusedMap1100swap_checked : acceptsGraphIso
    (fused (graph core1100) (root 8) 2 0) DegreeOneSmallSpectrum975.graph fusedMap1100swap=true := by decide +kernel
theorem certified1100swap : Certified (graph core1100) (root 8) 2 0 :=
  of_native_maps core1100 DegreeOneSmallSpectrum955.graph DegreeOneSmallSpectrum975.graph
    sourceMap1100swap fusedMap1100swap sourceMap1100swap_checked fusedMap1100swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1100
#print axioms sourceMap1100swap_checked
#print axioms fusedMap1100swap_checked
#print axioms certified1100swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
