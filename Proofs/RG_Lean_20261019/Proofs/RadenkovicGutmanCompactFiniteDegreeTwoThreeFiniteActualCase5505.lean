/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons110
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5505 : Family 3 := level3.get ⟨3,by decide⟩
def sourceMap5505 : (Vertices 3 ⊕ Fin 3 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,5,6,7,2,3,4,0,8,9,10,11] (sourceLabel 3 2 4 v)
def fusedMap5505 : (Vertices 3 ⊕ Fin 8) → Fin 12 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11] (fusedLabel 3 2 4 v)
theorem sourceMap5505_checked : acceptsGraphIso
    (source (graph core5505) (root 3) 2 4) SmallGeFourSpectrum110.graph sourceMap5505=true := by decide +kernel
theorem fusedMap5505_checked : acceptsGraphIso
    (fused (graph core5505) (root 3) 2 4) DegreeOneSmallSpectrum370.graph fusedMap5505=true := by decide +kernel
theorem certified5505 : Certified (graph core5505) (root 3) 2 4 :=
  of_native_maps core5505 SmallGeFourSpectrum110.graph DegreeOneSmallSpectrum370.graph
    sourceMap5505 fusedMap5505 sourceMap5505_checked fusedMap5505_checked
    DegreeTwoThreeFiniteComparisons.comparison5505
#print axioms sourceMap5505_checked
#print axioms fusedMap5505_checked
#print axioms certified5505
def sourceMap5505swap : (Vertices 3 ⊕ Fin 5 ⊕ Fin 3) → Fin 12 :=
  fun v => ![1,5,6,7,0,8,9,10,11,2,3,4] (sourceLabel 3 4 2 v)
def fusedMap5505swap : (Vertices 3 ⊕ Fin 8) → Fin 12 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11] (fusedLabel 3 4 2 v)
theorem sourceMap5505swap_checked : acceptsGraphIso
    (source (graph core5505) (root 3) 4 2) SmallGeFourSpectrum110.graph sourceMap5505swap=true := by decide +kernel
theorem fusedMap5505swap_checked : acceptsGraphIso
    (fused (graph core5505) (root 3) 4 2) DegreeOneSmallSpectrum370.graph fusedMap5505swap=true := by decide +kernel
theorem certified5505swap : Certified (graph core5505) (root 3) 4 2 :=
  of_native_maps core5505 SmallGeFourSpectrum110.graph DegreeOneSmallSpectrum370.graph
    sourceMap5505swap fusedMap5505swap sourceMap5505swap_checked fusedMap5505swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5505
#print axioms sourceMap5505swap_checked
#print axioms fusedMap5505swap_checked
#print axioms certified5505swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
