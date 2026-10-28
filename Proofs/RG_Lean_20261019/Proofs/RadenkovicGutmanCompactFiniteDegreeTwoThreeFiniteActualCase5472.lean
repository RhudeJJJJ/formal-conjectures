/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5472 : Family 5 := level5.get ⟨16,by decide⟩
def sourceMap5472 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (sourceLabel 5 0 4 v)
def fusedMap5472 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11] (fusedLabel 5 0 4 v)
theorem sourceMap5472_checked : acceptsGraphIso
    (source (graph core5472) (root 5) 0 4) SmallGeFourSpectrum095.graph sourceMap5472=true := by decide +kernel
theorem fusedMap5472_checked : acceptsGraphIso
    (fused (graph core5472) (root 5) 0 4) DegreeOneSmallSpectrum440.graph fusedMap5472=true := by decide +kernel
theorem certified5472 : Certified (graph core5472) (root 5) 0 4 :=
  of_native_maps core5472 SmallGeFourSpectrum095.graph DegreeOneSmallSpectrum440.graph
    sourceMap5472 fusedMap5472 sourceMap5472_checked fusedMap5472_checked
    DegreeTwoThreeFiniteComparisons.comparison5472
#print axioms sourceMap5472_checked
#print axioms fusedMap5472_checked
#print axioms certified5472
def sourceMap5472swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,8,9,10,11,7] (sourceLabel 5 4 0 v)
def fusedMap5472swap : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11] (fusedLabel 5 4 0 v)
theorem sourceMap5472swap_checked : acceptsGraphIso
    (source (graph core5472) (root 5) 4 0) SmallGeFourSpectrum095.graph sourceMap5472swap=true := by decide +kernel
theorem fusedMap5472swap_checked : acceptsGraphIso
    (fused (graph core5472) (root 5) 4 0) DegreeOneSmallSpectrum440.graph fusedMap5472swap=true := by decide +kernel
theorem certified5472swap : Certified (graph core5472) (root 5) 4 0 :=
  of_native_maps core5472 SmallGeFourSpectrum095.graph DegreeOneSmallSpectrum440.graph
    sourceMap5472swap fusedMap5472swap sourceMap5472swap_checked fusedMap5472swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5472
#print axioms sourceMap5472swap_checked
#print axioms fusedMap5472swap_checked
#print axioms certified5472swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
