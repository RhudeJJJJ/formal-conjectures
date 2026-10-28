/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5474 : Family 6 := level6.get ⟨18,by decide⟩
def sourceMap5474 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 6 0 4 v)
def fusedMap5474 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap5474_checked : acceptsGraphIso
    (source (graph core5474) (root 6) 0 4) DegreeOneSmallSpectrum972.graph sourceMap5474=true := by decide +kernel
theorem fusedMap5474_checked : acceptsGraphIso
    (fused (graph core5474) (root 6) 0 4) DegreeOneSmallSpectrum974.graph fusedMap5474=true := by decide +kernel
theorem certified5474 : Certified (graph core5474) (root 6) 0 4 :=
  of_native_maps core5474 DegreeOneSmallSpectrum972.graph DegreeOneSmallSpectrum974.graph
    sourceMap5474 fusedMap5474 sourceMap5474_checked fusedMap5474_checked
    DegreeTwoThreeFiniteComparisons.comparison5474
#print axioms sourceMap5474_checked
#print axioms fusedMap5474_checked
#print axioms certified5474
def sourceMap5474swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,8,9,10,11,12,7] (sourceLabel 6 4 0 v)
def fusedMap5474swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap5474swap_checked : acceptsGraphIso
    (source (graph core5474) (root 6) 4 0) DegreeOneSmallSpectrum972.graph sourceMap5474swap=true := by decide +kernel
theorem fusedMap5474swap_checked : acceptsGraphIso
    (fused (graph core5474) (root 6) 4 0) DegreeOneSmallSpectrum974.graph fusedMap5474swap=true := by decide +kernel
theorem certified5474swap : Certified (graph core5474) (root 6) 4 0 :=
  of_native_maps core5474 DegreeOneSmallSpectrum972.graph DegreeOneSmallSpectrum974.graph
    sourceMap5474swap fusedMap5474swap sourceMap5474swap_checked fusedMap5474swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5474
#print axioms sourceMap5474swap_checked
#print axioms fusedMap5474swap_checked
#print axioms certified5474swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
