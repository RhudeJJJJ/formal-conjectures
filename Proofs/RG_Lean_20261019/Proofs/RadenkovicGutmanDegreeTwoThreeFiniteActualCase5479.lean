/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5479 : Family 6 := level6.get ⟨42,by decide⟩
def sourceMap5479 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (sourceLabel 6 0 4 v)
def fusedMap5479 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap5479_checked : acceptsGraphIso
    (source (graph core5479) (root 6) 0 4) DegreeOneSmallSpectrum1090.graph sourceMap5479=true := by decide +kernel
theorem fusedMap5479_checked : acceptsGraphIso
    (fused (graph core5479) (root 6) 0 4) DegreeOneSmallSpectrum1095.graph fusedMap5479=true := by decide +kernel
theorem certified5479 : Certified (graph core5479) (root 6) 0 4 :=
  of_native_maps core5479 DegreeOneSmallSpectrum1090.graph DegreeOneSmallSpectrum1095.graph
    sourceMap5479 fusedMap5479 sourceMap5479_checked fusedMap5479_checked
    DegreeTwoThreeFiniteComparisons.comparison5479
#print axioms sourceMap5479_checked
#print axioms fusedMap5479_checked
#print axioms certified5479
def sourceMap5479swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,12,8] (sourceLabel 6 4 0 v)
def fusedMap5479swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap5479swap_checked : acceptsGraphIso
    (source (graph core5479) (root 6) 4 0) DegreeOneSmallSpectrum1090.graph sourceMap5479swap=true := by decide +kernel
theorem fusedMap5479swap_checked : acceptsGraphIso
    (fused (graph core5479) (root 6) 4 0) DegreeOneSmallSpectrum1095.graph fusedMap5479swap=true := by decide +kernel
theorem certified5479swap : Certified (graph core5479) (root 6) 4 0 :=
  of_native_maps core5479 DegreeOneSmallSpectrum1090.graph DegreeOneSmallSpectrum1095.graph
    sourceMap5479swap fusedMap5479swap sourceMap5479swap_checked fusedMap5479swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5479
#print axioms sourceMap5479swap_checked
#print axioms fusedMap5479swap_checked
#print axioms certified5479swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
