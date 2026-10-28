/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5457 : Family 3 := level3.get ⟨3,by decide⟩
def sourceMap5457 : (Vertices 3 ⊕ Fin 1 ⊕ Fin 3) → Fin 8 :=
  fun v => ![1,2,3,4,5,0,6,7] (sourceLabel 3 0 2 v)
def fusedMap5457 : (Vertices 3 ⊕ Fin 4) → Fin 8 :=
  fun v => ![1,2,3,4,0,5,6,7] (fusedLabel 3 0 2 v)
theorem sourceMap5457_checked : acceptsGraphIso
    (source (graph core5457) (root 3) 0 2) SmallGeFourSpectrum003.graph sourceMap5457=true := by decide +kernel
theorem fusedMap5457_checked : acceptsGraphIso
    (fused (graph core5457) (root 3) 0 2) DegreeOneSmallSpectrum017.graph fusedMap5457=true := by decide +kernel
theorem certified5457 : Certified (graph core5457) (root 3) 0 2 :=
  of_native_maps core5457 SmallGeFourSpectrum003.graph DegreeOneSmallSpectrum017.graph
    sourceMap5457 fusedMap5457 sourceMap5457_checked fusedMap5457_checked
    DegreeTwoThreeFiniteComparisons.comparison5457
#print axioms sourceMap5457_checked
#print axioms fusedMap5457_checked
#print axioms certified5457
def sourceMap5457swap : (Vertices 3 ⊕ Fin 3 ⊕ Fin 1) → Fin 8 :=
  fun v => ![1,2,3,4,0,6,7,5] (sourceLabel 3 2 0 v)
def fusedMap5457swap : (Vertices 3 ⊕ Fin 4) → Fin 8 :=
  fun v => ![1,2,3,4,0,5,6,7] (fusedLabel 3 2 0 v)
theorem sourceMap5457swap_checked : acceptsGraphIso
    (source (graph core5457) (root 3) 2 0) SmallGeFourSpectrum003.graph sourceMap5457swap=true := by decide +kernel
theorem fusedMap5457swap_checked : acceptsGraphIso
    (fused (graph core5457) (root 3) 2 0) DegreeOneSmallSpectrum017.graph fusedMap5457swap=true := by decide +kernel
theorem certified5457swap : Certified (graph core5457) (root 3) 2 0 :=
  of_native_maps core5457 SmallGeFourSpectrum003.graph DegreeOneSmallSpectrum017.graph
    sourceMap5457swap fusedMap5457swap sourceMap5457swap_checked fusedMap5457swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5457
#print axioms sourceMap5457swap_checked
#print axioms fusedMap5457swap_checked
#print axioms certified5457swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
