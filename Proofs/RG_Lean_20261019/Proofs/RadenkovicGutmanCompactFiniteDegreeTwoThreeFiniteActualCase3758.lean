/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3758 : Family 4 := level4.get ⟨3,by decide⟩
def sourceMap3758 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,1,2,3,9,7,8,4,5,6] (sourceLabel 4 1 2 v)
def fusedMap3758 : (Vertices 4 ⊕ Fin 5) → Fin 10 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9] (fusedLabel 4 1 2 v)
theorem sourceMap3758_checked : acceptsGraphIso
    (source (graph core3758) (root 4) 1 2) DegreeOneSmallSpectrum148.graph sourceMap3758=true := by decide +kernel
theorem fusedMap3758_checked : acceptsGraphIso
    (fused (graph core3758) (root 4) 1 2) DegreeOneSmallSpectrum090.graph fusedMap3758=true := by decide +kernel
theorem certified3758 : Certified (graph core3758) (root 4) 1 2 :=
  of_native_maps core3758 DegreeOneSmallSpectrum148.graph DegreeOneSmallSpectrum090.graph
    sourceMap3758 fusedMap3758 sourceMap3758_checked fusedMap3758_checked
    DegreeTwoThreeFiniteComparisons.comparison3758
#print axioms sourceMap3758_checked
#print axioms fusedMap3758_checked
#print axioms certified3758
def sourceMap3758swap : (Vertices 4 ⊕ Fin 3 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,1,2,3,9,4,5,6,7,8] (sourceLabel 4 2 1 v)
def fusedMap3758swap : (Vertices 4 ⊕ Fin 5) → Fin 10 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9] (fusedLabel 4 2 1 v)
theorem sourceMap3758swap_checked : acceptsGraphIso
    (source (graph core3758) (root 4) 2 1) DegreeOneSmallSpectrum148.graph sourceMap3758swap=true := by decide +kernel
theorem fusedMap3758swap_checked : acceptsGraphIso
    (fused (graph core3758) (root 4) 2 1) DegreeOneSmallSpectrum090.graph fusedMap3758swap=true := by decide +kernel
theorem certified3758swap : Certified (graph core3758) (root 4) 2 1 :=
  of_native_maps core3758 DegreeOneSmallSpectrum148.graph DegreeOneSmallSpectrum090.graph
    sourceMap3758swap fusedMap3758swap sourceMap3758swap_checked fusedMap3758swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3758
#print axioms sourceMap3758swap_checked
#print axioms fusedMap3758swap_checked
#print axioms certified3758swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
