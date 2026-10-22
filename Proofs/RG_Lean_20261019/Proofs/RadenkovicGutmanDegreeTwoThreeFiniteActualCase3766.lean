/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3766 : Family 4 := level4.get ⟨5,by decide⟩
def sourceMap3766 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,7,5,6,0,8,9,10,11] (sourceLabel 4 1 4 v)
def fusedMap3766 : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11] (fusedLabel 4 1 4 v)
theorem sourceMap3766_checked : acceptsGraphIso
    (source (graph core3766) (root 4) 1 4) DegreeOneSmallSpectrum429.graph sourceMap3766=true := by decide +kernel
theorem fusedMap3766_checked : acceptsGraphIso
    (fused (graph core3766) (root 4) 1 4) DegreeOneSmallSpectrum371.graph fusedMap3766=true := by decide +kernel
theorem certified3766 : Certified (graph core3766) (root 4) 1 4 :=
  of_native_maps core3766 DegreeOneSmallSpectrum429.graph DegreeOneSmallSpectrum371.graph
    sourceMap3766 fusedMap3766 sourceMap3766_checked fusedMap3766_checked
    DegreeTwoThreeFiniteComparisons.comparison3766
#print axioms sourceMap3766_checked
#print axioms fusedMap3766_checked
#print axioms certified3766
def sourceMap3766swap : (Vertices 4 ⊕ Fin 5 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,2,3,4,7,0,8,9,10,11,5,6] (sourceLabel 4 4 1 v)
def fusedMap3766swap : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11] (fusedLabel 4 4 1 v)
theorem sourceMap3766swap_checked : acceptsGraphIso
    (source (graph core3766) (root 4) 4 1) DegreeOneSmallSpectrum429.graph sourceMap3766swap=true := by decide +kernel
theorem fusedMap3766swap_checked : acceptsGraphIso
    (fused (graph core3766) (root 4) 4 1) DegreeOneSmallSpectrum371.graph fusedMap3766swap=true := by decide +kernel
theorem certified3766swap : Certified (graph core3766) (root 4) 4 1 :=
  of_native_maps core3766 DegreeOneSmallSpectrum429.graph DegreeOneSmallSpectrum371.graph
    sourceMap3766swap fusedMap3766swap sourceMap3766swap_checked fusedMap3766swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3766
#print axioms sourceMap3766swap_checked
#print axioms fusedMap3766swap_checked
#print axioms certified3766swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
