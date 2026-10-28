/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5486 : Family 3 := level3.get ⟨3,by decide⟩
def sourceMap5486 : (Vertices 3 ⊕ Fin 1 ⊕ Fin 7) → Fin 12 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11] (sourceLabel 3 0 6 v)
def fusedMap5486 : (Vertices 3 ⊕ Fin 8) → Fin 12 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11] (fusedLabel 3 0 6 v)
theorem sourceMap5486_checked : acceptsGraphIso
    (source (graph core5486) (root 3) 0 6) SmallGeFourSpectrum094.graph sourceMap5486=true := by decide +kernel
theorem fusedMap5486_checked : acceptsGraphIso
    (fused (graph core5486) (root 3) 0 6) DegreeOneSmallSpectrum370.graph fusedMap5486=true := by decide +kernel
theorem certified5486 : Certified (graph core5486) (root 3) 0 6 :=
  of_native_maps core5486 SmallGeFourSpectrum094.graph DegreeOneSmallSpectrum370.graph
    sourceMap5486 fusedMap5486 sourceMap5486_checked fusedMap5486_checked
    DegreeTwoThreeFiniteComparisons.comparison5486
#print axioms sourceMap5486_checked
#print axioms fusedMap5486_checked
#print axioms certified5486
def sourceMap5486swap : (Vertices 3 ⊕ Fin 7 ⊕ Fin 1) → Fin 12 :=
  fun v => ![3,4,5,6,2,1,0,8,9,10,11,7] (sourceLabel 3 6 0 v)
def fusedMap5486swap : (Vertices 3 ⊕ Fin 8) → Fin 12 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11] (fusedLabel 3 6 0 v)
theorem sourceMap5486swap_checked : acceptsGraphIso
    (source (graph core5486) (root 3) 6 0) SmallGeFourSpectrum094.graph sourceMap5486swap=true := by decide +kernel
theorem fusedMap5486swap_checked : acceptsGraphIso
    (fused (graph core5486) (root 3) 6 0) DegreeOneSmallSpectrum370.graph fusedMap5486swap=true := by decide +kernel
theorem certified5486swap : Certified (graph core5486) (root 3) 6 0 :=
  of_native_maps core5486 SmallGeFourSpectrum094.graph DegreeOneSmallSpectrum370.graph
    sourceMap5486swap fusedMap5486swap sourceMap5486swap_checked fusedMap5486swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5486
#print axioms sourceMap5486swap_checked
#print axioms fusedMap5486swap_checked
#print axioms certified5486swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
