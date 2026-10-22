/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5459 : Family 5 := level5.get ⟨12,by decide⟩
def sourceMap5459 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,1,2,3,7,8,9,4,5,6] (sourceLabel 5 0 2 v)
def fusedMap5459 : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 5 0 2 v)
theorem sourceMap5459_checked : acceptsGraphIso
    (source (graph core5459) (root 5) 0 2) SmallGeFourSpectrum023.graph sourceMap5459=true := by decide +kernel
theorem fusedMap5459_checked : acceptsGraphIso
    (fused (graph core5459) (root 5) 0 2) DegreeOneSmallSpectrum088.graph fusedMap5459=true := by decide +kernel
theorem certified5459 : Certified (graph core5459) (root 5) 0 2 :=
  of_native_maps core5459 SmallGeFourSpectrum023.graph DegreeOneSmallSpectrum088.graph
    sourceMap5459 fusedMap5459 sourceMap5459_checked fusedMap5459_checked
    DegreeTwoThreeFiniteComparisons.comparison5459
#print axioms sourceMap5459_checked
#print axioms fusedMap5459_checked
#print axioms certified5459
def sourceMap5459swap : (Vertices 5 ⊕ Fin 3 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,1,2,3,7,8,4,5,6,9] (sourceLabel 5 2 0 v)
def fusedMap5459swap : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 5 2 0 v)
theorem sourceMap5459swap_checked : acceptsGraphIso
    (source (graph core5459) (root 5) 2 0) SmallGeFourSpectrum023.graph sourceMap5459swap=true := by decide +kernel
theorem fusedMap5459swap_checked : acceptsGraphIso
    (fused (graph core5459) (root 5) 2 0) DegreeOneSmallSpectrum088.graph fusedMap5459swap=true := by decide +kernel
theorem certified5459swap : Certified (graph core5459) (root 5) 2 0 :=
  of_native_maps core5459 SmallGeFourSpectrum023.graph DegreeOneSmallSpectrum088.graph
    sourceMap5459swap fusedMap5459swap sourceMap5459swap_checked fusedMap5459swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5459
#print axioms sourceMap5459swap_checked
#print axioms fusedMap5459swap_checked
#print axioms certified5459swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
