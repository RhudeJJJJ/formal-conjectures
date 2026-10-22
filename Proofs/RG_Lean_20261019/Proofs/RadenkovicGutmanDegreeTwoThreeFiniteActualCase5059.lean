/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5059 : Family 4 := level4.get ⟨6,by decide⟩
def sourceMap5059 : (Vertices 4 ⊕ Fin 3 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,5,6,7,8,2,3,4,0,9,10,11,12] (sourceLabel 4 2 4 v)
def fusedMap5059 : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12] (fusedLabel 4 2 4 v)
theorem sourceMap5059_checked : acceptsGraphIso
    (source (graph core5059) (root 4) 2 4) DegreeOneSmallSpectrum1478.graph sourceMap5059=true := by decide +kernel
theorem fusedMap5059_checked : acceptsGraphIso
    (fused (graph core5059) (root 4) 2 4) DegreeOneSmallSpectrum915.graph fusedMap5059=true := by decide +kernel
theorem certified5059 : Certified (graph core5059) (root 4) 2 4 :=
  of_native_maps core5059 DegreeOneSmallSpectrum1478.graph DegreeOneSmallSpectrum915.graph
    sourceMap5059 fusedMap5059 sourceMap5059_checked fusedMap5059_checked
    DegreeTwoThreeFiniteComparisons.comparison5059
#print axioms sourceMap5059_checked
#print axioms fusedMap5059_checked
#print axioms certified5059
def sourceMap5059swap : (Vertices 4 ⊕ Fin 5 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,5,6,7,8,0,9,10,11,12,2,3,4] (sourceLabel 4 4 2 v)
def fusedMap5059swap : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12] (fusedLabel 4 4 2 v)
theorem sourceMap5059swap_checked : acceptsGraphIso
    (source (graph core5059) (root 4) 4 2) DegreeOneSmallSpectrum1478.graph sourceMap5059swap=true := by decide +kernel
theorem fusedMap5059swap_checked : acceptsGraphIso
    (fused (graph core5059) (root 4) 4 2) DegreeOneSmallSpectrum915.graph fusedMap5059swap=true := by decide +kernel
theorem certified5059swap : Certified (graph core5059) (root 4) 4 2 :=
  of_native_maps core5059 DegreeOneSmallSpectrum1478.graph DegreeOneSmallSpectrum915.graph
    sourceMap5059swap fusedMap5059swap sourceMap5059swap_checked fusedMap5059swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5059
#print axioms sourceMap5059swap_checked
#print axioms fusedMap5059swap_checked
#print axioms certified5059swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
