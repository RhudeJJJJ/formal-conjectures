/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5464 : Family 6 := level6.get ⟨32,by decide⟩
def sourceMap5464 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,8,9,10,5,6,7] (sourceLabel 6 0 2 v)
def fusedMap5464 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 0 2 v)
theorem sourceMap5464_checked : acceptsGraphIso
    (source (graph core5464) (root 6) 0 2) SmallGeFourSpectrum066.graph sourceMap5464=true := by decide +kernel
theorem fusedMap5464_checked : acceptsGraphIso
    (fused (graph core5464) (root 6) 0 2) DegreeOneSmallSpectrum209.graph fusedMap5464=true := by decide +kernel
theorem certified5464 : Certified (graph core5464) (root 6) 0 2 :=
  of_native_maps core5464 SmallGeFourSpectrum066.graph DegreeOneSmallSpectrum209.graph
    sourceMap5464 fusedMap5464 sourceMap5464_checked fusedMap5464_checked
    DegreeTwoThreeFiniteComparisons.comparison5464
#print axioms sourceMap5464_checked
#print axioms fusedMap5464_checked
#print axioms certified5464
def sourceMap5464swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,8,9,5,6,7,10] (sourceLabel 6 2 0 v)
def fusedMap5464swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 2 0 v)
theorem sourceMap5464swap_checked : acceptsGraphIso
    (source (graph core5464) (root 6) 2 0) SmallGeFourSpectrum066.graph sourceMap5464swap=true := by decide +kernel
theorem fusedMap5464swap_checked : acceptsGraphIso
    (fused (graph core5464) (root 6) 2 0) DegreeOneSmallSpectrum209.graph fusedMap5464swap=true := by decide +kernel
theorem certified5464swap : Certified (graph core5464) (root 6) 2 0 :=
  of_native_maps core5464 SmallGeFourSpectrum066.graph DegreeOneSmallSpectrum209.graph
    sourceMap5464swap fusedMap5464swap sourceMap5464swap_checked fusedMap5464swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5464
#print axioms sourceMap5464swap_checked
#print axioms fusedMap5464swap_checked
#print axioms certified5464swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
