/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5473 : Family 5 := level5.get ⟨17,by decide⟩
def sourceMap5473 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (sourceLabel 5 0 4 v)
def fusedMap5473 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11] (fusedLabel 5 0 4 v)
theorem sourceMap5473_checked : acceptsGraphIso
    (source (graph core5473) (root 5) 0 4) SmallGeFourSpectrum099.graph sourceMap5473=true := by decide +kernel
theorem fusedMap5473_checked : acceptsGraphIso
    (fused (graph core5473) (root 5) 0 4) DegreeOneSmallSpectrum505.graph fusedMap5473=true := by decide +kernel
theorem certified5473 : Certified (graph core5473) (root 5) 0 4 :=
  of_native_maps core5473 SmallGeFourSpectrum099.graph DegreeOneSmallSpectrum505.graph
    sourceMap5473 fusedMap5473 sourceMap5473_checked fusedMap5473_checked
    DegreeTwoThreeFiniteComparisons.comparison5473
#print axioms sourceMap5473_checked
#print axioms fusedMap5473_checked
#print axioms certified5473
def sourceMap5473swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,8,9,10,11,7] (sourceLabel 5 4 0 v)
def fusedMap5473swap : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11] (fusedLabel 5 4 0 v)
theorem sourceMap5473swap_checked : acceptsGraphIso
    (source (graph core5473) (root 5) 4 0) SmallGeFourSpectrum099.graph sourceMap5473swap=true := by decide +kernel
theorem fusedMap5473swap_checked : acceptsGraphIso
    (fused (graph core5473) (root 5) 4 0) DegreeOneSmallSpectrum505.graph fusedMap5473swap=true := by decide +kernel
theorem certified5473swap : Certified (graph core5473) (root 5) 4 0 :=
  of_native_maps core5473 SmallGeFourSpectrum099.graph DegreeOneSmallSpectrum505.graph
    sourceMap5473swap fusedMap5473swap sourceMap5473swap_checked fusedMap5473swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5473
#print axioms sourceMap5473swap_checked
#print axioms fusedMap5473swap_checked
#print axioms certified5473swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
