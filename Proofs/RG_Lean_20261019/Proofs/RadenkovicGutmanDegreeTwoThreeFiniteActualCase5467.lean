/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5467 : Family 6 := level6.get ⟨42,by decide⟩
def sourceMap5467 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 6 0 2 v)
def fusedMap5467 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10] (fusedLabel 6 0 2 v)
theorem sourceMap5467_checked : acceptsGraphIso
    (source (graph core5467) (root 6) 0 2) SmallGeFourSpectrum047.graph sourceMap5467=true := by decide +kernel
theorem fusedMap5467_checked : acceptsGraphIso
    (fused (graph core5467) (root 6) 0 2) DegreeOneSmallSpectrum275.graph fusedMap5467=true := by decide +kernel
theorem certified5467 : Certified (graph core5467) (root 6) 0 2 :=
  of_native_maps core5467 SmallGeFourSpectrum047.graph DegreeOneSmallSpectrum275.graph
    sourceMap5467 fusedMap5467 sourceMap5467_checked fusedMap5467_checked
    DegreeTwoThreeFiniteComparisons.comparison5467
#print axioms sourceMap5467_checked
#print axioms fusedMap5467_checked
#print axioms certified5467
def sourceMap5467swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,8,9,10,7] (sourceLabel 6 2 0 v)
def fusedMap5467swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10] (fusedLabel 6 2 0 v)
theorem sourceMap5467swap_checked : acceptsGraphIso
    (source (graph core5467) (root 6) 2 0) SmallGeFourSpectrum047.graph sourceMap5467swap=true := by decide +kernel
theorem fusedMap5467swap_checked : acceptsGraphIso
    (fused (graph core5467) (root 6) 2 0) DegreeOneSmallSpectrum275.graph fusedMap5467swap=true := by decide +kernel
theorem certified5467swap : Certified (graph core5467) (root 6) 2 0 :=
  of_native_maps core5467 SmallGeFourSpectrum047.graph DegreeOneSmallSpectrum275.graph
    sourceMap5467swap fusedMap5467swap sourceMap5467swap_checked fusedMap5467swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5467
#print axioms sourceMap5467swap_checked
#print axioms fusedMap5467swap_checked
#print axioms certified5467swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
