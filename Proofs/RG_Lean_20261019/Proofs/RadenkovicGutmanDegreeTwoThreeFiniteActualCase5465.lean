/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5465 : Family 6 := level6.get ⟨35,by decide⟩
def sourceMap5465 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,7,8,9,10,4,5,6] (sourceLabel 6 0 2 v)
def fusedMap5465 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 0 2 v)
theorem sourceMap5465_checked : acceptsGraphIso
    (source (graph core5465) (root 6) 0 2) SmallGeFourSpectrum067.graph sourceMap5465=true := by decide +kernel
theorem fusedMap5465_checked : acceptsGraphIso
    (fused (graph core5465) (root 6) 0 2) DegreeOneSmallSpectrum220.graph fusedMap5465=true := by decide +kernel
theorem certified5465 : Certified (graph core5465) (root 6) 0 2 :=
  of_native_maps core5465 SmallGeFourSpectrum067.graph DegreeOneSmallSpectrum220.graph
    sourceMap5465 fusedMap5465 sourceMap5465_checked fusedMap5465_checked
    DegreeTwoThreeFiniteComparisons.comparison5465
#print axioms sourceMap5465_checked
#print axioms fusedMap5465_checked
#print axioms certified5465
def sourceMap5465swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,7,8,9,4,5,6,10] (sourceLabel 6 2 0 v)
def fusedMap5465swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 2 0 v)
theorem sourceMap5465swap_checked : acceptsGraphIso
    (source (graph core5465) (root 6) 2 0) SmallGeFourSpectrum067.graph sourceMap5465swap=true := by decide +kernel
theorem fusedMap5465swap_checked : acceptsGraphIso
    (fused (graph core5465) (root 6) 2 0) DegreeOneSmallSpectrum220.graph fusedMap5465swap=true := by decide +kernel
theorem certified5465swap : Certified (graph core5465) (root 6) 2 0 :=
  of_native_maps core5465 SmallGeFourSpectrum067.graph DegreeOneSmallSpectrum220.graph
    sourceMap5465swap fusedMap5465swap sourceMap5465swap_checked fusedMap5465swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5465
#print axioms sourceMap5465swap_checked
#print axioms fusedMap5465swap_checked
#print axioms certified5465swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
