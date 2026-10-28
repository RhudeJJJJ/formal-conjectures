/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5481 : Family 3 := level3.get ⟨3,by decide⟩
def sourceMap5481 : (Vertices 3 ⊕ Fin 1 ⊕ Fin 6) → Fin 11 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10] (sourceLabel 3 0 5 v)
def fusedMap5481 : (Vertices 3 ⊕ Fin 7) → Fin 11 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10] (fusedLabel 3 0 5 v)
theorem sourceMap5481_checked : acceptsGraphIso
    (source (graph core5481) (root 3) 0 5) SmallGeFourSpectrum037.graph sourceMap5481=true := by decide +kernel
theorem fusedMap5481_checked : acceptsGraphIso
    (fused (graph core5481) (root 3) 0 5) DegreeOneSmallSpectrum175.graph fusedMap5481=true := by decide +kernel
theorem certified5481 : Certified (graph core5481) (root 3) 0 5 :=
  of_native_maps core5481 SmallGeFourSpectrum037.graph DegreeOneSmallSpectrum175.graph
    sourceMap5481 fusedMap5481 sourceMap5481_checked fusedMap5481_checked
    DegreeTwoThreeFiniteComparisons.comparison5481
#print axioms sourceMap5481_checked
#print axioms fusedMap5481_checked
#print axioms certified5481
def sourceMap5481swap : (Vertices 3 ⊕ Fin 6 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,3,4,5,1,0,7,8,9,10,6] (sourceLabel 3 5 0 v)
def fusedMap5481swap : (Vertices 3 ⊕ Fin 7) → Fin 11 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10] (fusedLabel 3 5 0 v)
theorem sourceMap5481swap_checked : acceptsGraphIso
    (source (graph core5481) (root 3) 5 0) SmallGeFourSpectrum037.graph sourceMap5481swap=true := by decide +kernel
theorem fusedMap5481swap_checked : acceptsGraphIso
    (fused (graph core5481) (root 3) 5 0) DegreeOneSmallSpectrum175.graph fusedMap5481swap=true := by decide +kernel
theorem certified5481swap : Certified (graph core5481) (root 3) 5 0 :=
  of_native_maps core5481 SmallGeFourSpectrum037.graph DegreeOneSmallSpectrum175.graph
    sourceMap5481swap fusedMap5481swap sourceMap5481swap_checked fusedMap5481swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5481
#print axioms sourceMap5481swap_checked
#print axioms fusedMap5481swap_checked
#print axioms certified5481swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
