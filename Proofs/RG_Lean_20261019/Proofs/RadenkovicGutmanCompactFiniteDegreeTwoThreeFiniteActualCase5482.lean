/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5482 : Family 4 := level4.get ⟨7,by decide⟩
def sourceMap5482 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 6) → Fin 12 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11] (sourceLabel 4 0 5 v)
def fusedMap5482 : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11] (fusedLabel 4 0 5 v)
theorem sourceMap5482_checked : acceptsGraphIso
    (source (graph core5482) (root 4) 0 5) SmallGeFourSpectrum104.graph sourceMap5482=true := by decide +kernel
theorem fusedMap5482_checked : acceptsGraphIso
    (fused (graph core5482) (root 4) 0 5) DegreeOneSmallSpectrum380.graph fusedMap5482=true := by decide +kernel
theorem certified5482 : Certified (graph core5482) (root 4) 0 5 :=
  of_native_maps core5482 SmallGeFourSpectrum104.graph DegreeOneSmallSpectrum380.graph
    sourceMap5482 fusedMap5482 sourceMap5482_checked fusedMap5482_checked
    DegreeTwoThreeFiniteComparisons.comparison5482
#print axioms sourceMap5482_checked
#print axioms fusedMap5482_checked
#print axioms certified5482
def sourceMap5482swap : (Vertices 4 ⊕ Fin 6 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,8,9,10,11,7] (sourceLabel 4 5 0 v)
def fusedMap5482swap : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11] (fusedLabel 4 5 0 v)
theorem sourceMap5482swap_checked : acceptsGraphIso
    (source (graph core5482) (root 4) 5 0) SmallGeFourSpectrum104.graph sourceMap5482swap=true := by decide +kernel
theorem fusedMap5482swap_checked : acceptsGraphIso
    (fused (graph core5482) (root 4) 5 0) DegreeOneSmallSpectrum380.graph fusedMap5482swap=true := by decide +kernel
theorem certified5482swap : Certified (graph core5482) (root 4) 5 0 :=
  of_native_maps core5482 SmallGeFourSpectrum104.graph DegreeOneSmallSpectrum380.graph
    sourceMap5482swap fusedMap5482swap sourceMap5482swap_checked fusedMap5482swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5482
#print axioms sourceMap5482swap_checked
#print axioms fusedMap5482swap_checked
#print axioms certified5482swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
