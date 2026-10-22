/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3636 : Family 3 := level3.get ⟨2,by decide⟩
def sourceMap3636 : (Vertices 3 ⊕ Fin 1 ⊕ Fin 8) → Fin 13 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12] (sourceLabel 3 0 7 v)
def fusedMap3636 : (Vertices 3 ⊕ Fin 9) → Fin 13 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11,12] (fusedLabel 3 0 7 v)
theorem sourceMap3636_checked : acceptsGraphIso
    (source (graph core3636) (root 3) 0 7) DegreeOneSmallSpectrum922.graph sourceMap3636=true := by decide +kernel
theorem fusedMap3636_checked : acceptsGraphIso
    (fused (graph core3636) (root 3) 0 7) DegreeOneSmallSpectrum857.graph fusedMap3636=true := by decide +kernel
theorem certified3636 : Certified (graph core3636) (root 3) 0 7 :=
  of_native_maps core3636 DegreeOneSmallSpectrum922.graph DegreeOneSmallSpectrum857.graph
    sourceMap3636 fusedMap3636 sourceMap3636_checked fusedMap3636_checked
    DegreeTwoThreeFiniteComparisons.comparison3636
#print axioms sourceMap3636_checked
#print axioms fusedMap3636_checked
#print axioms certified3636
def sourceMap3636swap : (Vertices 3 ⊕ Fin 8 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,4,5,6,2,1,0,8,9,10,11,12,7] (sourceLabel 3 7 0 v)
def fusedMap3636swap : (Vertices 3 ⊕ Fin 9) → Fin 13 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11,12] (fusedLabel 3 7 0 v)
theorem sourceMap3636swap_checked : acceptsGraphIso
    (source (graph core3636) (root 3) 7 0) DegreeOneSmallSpectrum922.graph sourceMap3636swap=true := by decide +kernel
theorem fusedMap3636swap_checked : acceptsGraphIso
    (fused (graph core3636) (root 3) 7 0) DegreeOneSmallSpectrum857.graph fusedMap3636swap=true := by decide +kernel
theorem certified3636swap : Certified (graph core3636) (root 3) 7 0 :=
  of_native_maps core3636 DegreeOneSmallSpectrum922.graph DegreeOneSmallSpectrum857.graph
    sourceMap3636swap fusedMap3636swap sourceMap3636swap_checked fusedMap3636swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3636
#print axioms sourceMap3636swap_checked
#print axioms fusedMap3636swap_checked
#print axioms certified3636swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
