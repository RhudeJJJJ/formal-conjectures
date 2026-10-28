/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5320 : Family 4 := level4.get ⟨5,by decide⟩
def sourceMap5320 : (Vertices 4 ⊕ Fin 3 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,7,8,9,10,4,5,6,2,1,0,11,12,13,14,15,16] (sourceLabel 4 2 8 v)
def fusedMap5320 : (Vertices 4 ⊕ Fin 12) → Fin 17 :=
  fun v => ![5,6,7,8,9,4,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 4 2 8 v)
theorem sourceMap5320_checked : acceptsGraphIso
    (source (graph core5320) (root 4) 2 8) DegreeTwoThreeSpectrum5679.graph sourceMap5320=true := by decide +kernel
theorem fusedMap5320_checked : acceptsGraphIso
    (fused (graph core5320) (root 4) 2 8) DegreeTwoThreeSpectrum4980.graph fusedMap5320=true := by decide +kernel
theorem certified5320 : Certified (graph core5320) (root 4) 2 8 :=
  of_native_maps core5320 DegreeTwoThreeSpectrum5679.graph DegreeTwoThreeSpectrum4980.graph
    sourceMap5320 fusedMap5320 sourceMap5320_checked fusedMap5320_checked
    DegreeTwoThreeFiniteComparisons.comparison5320
#print axioms sourceMap5320_checked
#print axioms fusedMap5320_checked
#print axioms certified5320
def sourceMap5320swap : (Vertices 4 ⊕ Fin 9 ⊕ Fin 3) → Fin 17 :=
  fun v => ![3,7,8,9,10,2,1,0,11,12,13,14,15,16,4,5,6] (sourceLabel 4 8 2 v)
def fusedMap5320swap : (Vertices 4 ⊕ Fin 12) → Fin 17 :=
  fun v => ![5,6,7,8,9,4,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 4 8 2 v)
theorem sourceMap5320swap_checked : acceptsGraphIso
    (source (graph core5320) (root 4) 8 2) DegreeTwoThreeSpectrum5679.graph sourceMap5320swap=true := by decide +kernel
theorem fusedMap5320swap_checked : acceptsGraphIso
    (fused (graph core5320) (root 4) 8 2) DegreeTwoThreeSpectrum4980.graph fusedMap5320swap=true := by decide +kernel
theorem certified5320swap : Certified (graph core5320) (root 4) 8 2 :=
  of_native_maps core5320 DegreeTwoThreeSpectrum5679.graph DegreeTwoThreeSpectrum4980.graph
    sourceMap5320swap fusedMap5320swap sourceMap5320swap_checked fusedMap5320swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5320
#print axioms sourceMap5320swap_checked
#print axioms fusedMap5320swap_checked
#print axioms certified5320swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
