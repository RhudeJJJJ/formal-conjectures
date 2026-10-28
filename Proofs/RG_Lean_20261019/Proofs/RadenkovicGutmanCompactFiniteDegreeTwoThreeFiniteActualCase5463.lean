/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5463 : Family 6 := level6.get ⟨26,by decide⟩
def sourceMap5463 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,8,9,10,5,6,7] (sourceLabel 6 0 2 v)
def fusedMap5463 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 0 2 v)
theorem sourceMap5463_checked : acceptsGraphIso
    (source (graph core5463) (root 6) 0 2) SmallGeFourSpectrum054.graph sourceMap5463=true := by decide +kernel
theorem fusedMap5463_checked : acceptsGraphIso
    (fused (graph core5463) (root 6) 0 2) DegreeOneSmallSpectrum184.graph fusedMap5463=true := by decide +kernel
theorem certified5463 : Certified (graph core5463) (root 6) 0 2 :=
  of_native_maps core5463 SmallGeFourSpectrum054.graph DegreeOneSmallSpectrum184.graph
    sourceMap5463 fusedMap5463 sourceMap5463_checked fusedMap5463_checked
    DegreeTwoThreeFiniteComparisons.comparison5463
#print axioms sourceMap5463_checked
#print axioms fusedMap5463_checked
#print axioms certified5463
def sourceMap5463swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,8,9,5,6,7,10] (sourceLabel 6 2 0 v)
def fusedMap5463swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 2 0 v)
theorem sourceMap5463swap_checked : acceptsGraphIso
    (source (graph core5463) (root 6) 2 0) SmallGeFourSpectrum054.graph sourceMap5463swap=true := by decide +kernel
theorem fusedMap5463swap_checked : acceptsGraphIso
    (fused (graph core5463) (root 6) 2 0) DegreeOneSmallSpectrum184.graph fusedMap5463swap=true := by decide +kernel
theorem certified5463swap : Certified (graph core5463) (root 6) 2 0 :=
  of_native_maps core5463 SmallGeFourSpectrum054.graph DegreeOneSmallSpectrum184.graph
    sourceMap5463swap fusedMap5463swap sourceMap5463swap_checked fusedMap5463swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5463
#print axioms sourceMap5463swap_checked
#print axioms fusedMap5463swap_checked
#print axioms certified5463swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
