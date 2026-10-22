/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5491 : Family 4 := level4.get ⟨7,by decide⟩
def sourceMap5491 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,6,7,4,5,0,8,9,10,11] (sourceLabel 4 1 4 v)
def fusedMap5491 : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11] (fusedLabel 4 1 4 v)
theorem sourceMap5491_checked : acceptsGraphIso
    (source (graph core5491) (root 4) 1 4) SmallGeFourSpectrum099.graph sourceMap5491=true := by decide +kernel
theorem fusedMap5491_checked : acceptsGraphIso
    (fused (graph core5491) (root 4) 1 4) DegreeOneSmallSpectrum380.graph fusedMap5491=true := by decide +kernel
theorem certified5491 : Certified (graph core5491) (root 4) 1 4 :=
  of_native_maps core5491 SmallGeFourSpectrum099.graph DegreeOneSmallSpectrum380.graph
    sourceMap5491 fusedMap5491 sourceMap5491_checked fusedMap5491_checked
    DegreeTwoThreeFiniteComparisons.comparison5491
#print axioms sourceMap5491_checked
#print axioms fusedMap5491_checked
#print axioms certified5491
def sourceMap5491swap : (Vertices 4 ⊕ Fin 5 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,2,3,6,7,0,8,9,10,11,4,5] (sourceLabel 4 4 1 v)
def fusedMap5491swap : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11] (fusedLabel 4 4 1 v)
theorem sourceMap5491swap_checked : acceptsGraphIso
    (source (graph core5491) (root 4) 4 1) SmallGeFourSpectrum099.graph sourceMap5491swap=true := by decide +kernel
theorem fusedMap5491swap_checked : acceptsGraphIso
    (fused (graph core5491) (root 4) 4 1) DegreeOneSmallSpectrum380.graph fusedMap5491swap=true := by decide +kernel
theorem certified5491swap : Certified (graph core5491) (root 4) 4 1 :=
  of_native_maps core5491 SmallGeFourSpectrum099.graph DegreeOneSmallSpectrum380.graph
    sourceMap5491swap fusedMap5491swap sourceMap5491swap_checked fusedMap5491swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5491
#print axioms sourceMap5491swap_checked
#print axioms fusedMap5491swap_checked
#print axioms certified5491swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
