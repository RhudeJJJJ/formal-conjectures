/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5462 : Family 6 := level6.get ⟨18,by decide⟩
def sourceMap5462 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,7,8,9,10,4,5,6,1,2,3] (sourceLabel 6 0 2 v)
def fusedMap5462 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,9,10,5,6,7,8] (fusedLabel 6 0 2 v)
theorem sourceMap5462_checked : acceptsGraphIso
    (source (graph core5462) (root 6) 0 2) SmallGeFourSpectrum039.graph sourceMap5462=true := by decide +kernel
theorem fusedMap5462_checked : acceptsGraphIso
    (fused (graph core5462) (root 6) 0 2) DegreeOneSmallSpectrum229.graph fusedMap5462=true := by decide +kernel
theorem certified5462 : Certified (graph core5462) (root 6) 0 2 :=
  of_native_maps core5462 SmallGeFourSpectrum039.graph DegreeOneSmallSpectrum229.graph
    sourceMap5462 fusedMap5462 sourceMap5462_checked fusedMap5462_checked
    DegreeTwoThreeFiniteComparisons.comparison5462
#print axioms sourceMap5462_checked
#print axioms fusedMap5462_checked
#print axioms certified5462
def sourceMap5462swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,7,8,9,10,4,5,1,2,3,6] (sourceLabel 6 2 0 v)
def fusedMap5462swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,9,10,5,6,7,8] (fusedLabel 6 2 0 v)
theorem sourceMap5462swap_checked : acceptsGraphIso
    (source (graph core5462) (root 6) 2 0) SmallGeFourSpectrum039.graph sourceMap5462swap=true := by decide +kernel
theorem fusedMap5462swap_checked : acceptsGraphIso
    (fused (graph core5462) (root 6) 2 0) DegreeOneSmallSpectrum229.graph fusedMap5462swap=true := by decide +kernel
theorem certified5462swap : Certified (graph core5462) (root 6) 2 0 :=
  of_native_maps core5462 SmallGeFourSpectrum039.graph DegreeOneSmallSpectrum229.graph
    sourceMap5462swap fusedMap5462swap sourceMap5462swap_checked fusedMap5462swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5462
#print axioms sourceMap5462swap_checked
#print axioms fusedMap5462swap_checked
#print axioms certified5462swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
