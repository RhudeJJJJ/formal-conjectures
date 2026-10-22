/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5468 : Family 6 := level6.get ⟨44,by decide⟩
def sourceMap5468 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 6 0 2 v)
def fusedMap5468 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10] (fusedLabel 6 0 2 v)
theorem sourceMap5468_checked : acceptsGraphIso
    (source (graph core5468) (root 6) 0 2) SmallGeFourSpectrum055.graph sourceMap5468=true := by decide +kernel
theorem fusedMap5468_checked : acceptsGraphIso
    (fused (graph core5468) (root 6) 0 2) DegreeOneSmallSpectrum318.graph fusedMap5468=true := by decide +kernel
theorem certified5468 : Certified (graph core5468) (root 6) 0 2 :=
  of_native_maps core5468 SmallGeFourSpectrum055.graph DegreeOneSmallSpectrum318.graph
    sourceMap5468 fusedMap5468 sourceMap5468_checked fusedMap5468_checked
    DegreeTwoThreeFiniteComparisons.comparison5468
#print axioms sourceMap5468_checked
#print axioms fusedMap5468_checked
#print axioms certified5468
def sourceMap5468swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,8,9,10,7] (sourceLabel 6 2 0 v)
def fusedMap5468swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10] (fusedLabel 6 2 0 v)
theorem sourceMap5468swap_checked : acceptsGraphIso
    (source (graph core5468) (root 6) 2 0) SmallGeFourSpectrum055.graph sourceMap5468swap=true := by decide +kernel
theorem fusedMap5468swap_checked : acceptsGraphIso
    (fused (graph core5468) (root 6) 2 0) DegreeOneSmallSpectrum318.graph fusedMap5468swap=true := by decide +kernel
theorem certified5468swap : Certified (graph core5468) (root 6) 2 0 :=
  of_native_maps core5468 SmallGeFourSpectrum055.graph DegreeOneSmallSpectrum318.graph
    sourceMap5468swap fusedMap5468swap sourceMap5468swap_checked fusedMap5468swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5468
#print axioms sourceMap5468swap_checked
#print axioms fusedMap5468swap_checked
#print axioms certified5468swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
