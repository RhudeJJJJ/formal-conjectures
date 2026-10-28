/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5480 : Family 6 := level6.get ⟨44,by decide⟩
def sourceMap5480 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (sourceLabel 6 0 4 v)
def fusedMap5480 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap5480_checked : acceptsGraphIso
    (source (graph core5480) (root 6) 0 4) DegreeOneSmallSpectrum1292.graph sourceMap5480=true := by decide +kernel
theorem fusedMap5480_checked : acceptsGraphIso
    (fused (graph core5480) (root 6) 0 4) DegreeOneSmallSpectrum1296.graph fusedMap5480=true := by decide +kernel
theorem certified5480 : Certified (graph core5480) (root 6) 0 4 :=
  of_native_maps core5480 DegreeOneSmallSpectrum1292.graph DegreeOneSmallSpectrum1296.graph
    sourceMap5480 fusedMap5480 sourceMap5480_checked fusedMap5480_checked
    DegreeTwoThreeFiniteComparisons.comparison5480
#print axioms sourceMap5480_checked
#print axioms fusedMap5480_checked
#print axioms certified5480
def sourceMap5480swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,12,8] (sourceLabel 6 4 0 v)
def fusedMap5480swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap5480swap_checked : acceptsGraphIso
    (source (graph core5480) (root 6) 4 0) DegreeOneSmallSpectrum1292.graph sourceMap5480swap=true := by decide +kernel
theorem fusedMap5480swap_checked : acceptsGraphIso
    (fused (graph core5480) (root 6) 4 0) DegreeOneSmallSpectrum1296.graph fusedMap5480swap=true := by decide +kernel
theorem certified5480swap : Certified (graph core5480) (root 6) 4 0 :=
  of_native_maps core5480 DegreeOneSmallSpectrum1292.graph DegreeOneSmallSpectrum1296.graph
    sourceMap5480swap fusedMap5480swap sourceMap5480swap_checked fusedMap5480swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5480
#print axioms sourceMap5480swap_checked
#print axioms fusedMap5480swap_checked
#print axioms certified5480swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
