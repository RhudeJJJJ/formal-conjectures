/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3759 : Family 4 := level4.get ⟨5,by decide⟩
def sourceMap3759 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,1,2,3,6,4,5,7,8,9] (sourceLabel 4 1 2 v)
def fusedMap3759 : (Vertices 4 ⊕ Fin 5) → Fin 10 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9] (fusedLabel 4 1 2 v)
theorem sourceMap3759_checked : acceptsGraphIso
    (source (graph core3759) (root 4) 1 2) DegreeOneSmallSpectrum108.graph sourceMap3759=true := by decide +kernel
theorem fusedMap3759_checked : acceptsGraphIso
    (fused (graph core3759) (root 4) 1 2) DegreeOneSmallSpectrum075.graph fusedMap3759=true := by decide +kernel
theorem certified3759 : Certified (graph core3759) (root 4) 1 2 :=
  of_native_maps core3759 DegreeOneSmallSpectrum108.graph DegreeOneSmallSpectrum075.graph
    sourceMap3759 fusedMap3759 sourceMap3759_checked fusedMap3759_checked
    DegreeTwoThreeFiniteComparisons.comparison3759
#print axioms sourceMap3759_checked
#print axioms fusedMap3759_checked
#print axioms certified3759
def sourceMap3759swap : (Vertices 4 ⊕ Fin 3 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,1,2,3,6,7,8,9,4,5] (sourceLabel 4 2 1 v)
def fusedMap3759swap : (Vertices 4 ⊕ Fin 5) → Fin 10 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9] (fusedLabel 4 2 1 v)
theorem sourceMap3759swap_checked : acceptsGraphIso
    (source (graph core3759) (root 4) 2 1) DegreeOneSmallSpectrum108.graph sourceMap3759swap=true := by decide +kernel
theorem fusedMap3759swap_checked : acceptsGraphIso
    (fused (graph core3759) (root 4) 2 1) DegreeOneSmallSpectrum075.graph fusedMap3759swap=true := by decide +kernel
theorem certified3759swap : Certified (graph core3759) (root 4) 2 1 :=
  of_native_maps core3759 DegreeOneSmallSpectrum108.graph DegreeOneSmallSpectrum075.graph
    sourceMap3759swap fusedMap3759swap sourceMap3759swap_checked fusedMap3759swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3759
#print axioms sourceMap3759swap_checked
#print axioms fusedMap3759swap_checked
#print axioms certified3759swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
