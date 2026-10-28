/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5301 : Family 6 := level6.get ⟨33,by decide⟩
def sourceMap5301 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (sourceLabel 6 2 6 v)
def fusedMap5301 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 2 6 v)
theorem sourceMap5301_checked : acceptsGraphIso
    (source (graph core5301) (root 6) 2 6) DegreeTwoThreeSpectrum6798.graph sourceMap5301=true := by decide +kernel
theorem fusedMap5301_checked : acceptsGraphIso
    (fused (graph core5301) (root 6) 2 6) DegreeTwoThreeSpectrum5048.graph fusedMap5301=true := by decide +kernel
theorem certified5301 : Certified (graph core5301) (root 6) 2 6 :=
  of_native_maps core5301 DegreeTwoThreeSpectrum6798.graph DegreeTwoThreeSpectrum5048.graph
    sourceMap5301 fusedMap5301 sourceMap5301_checked fusedMap5301_checked
    DegreeTwoThreeFiniteComparisons.comparison5301
#print axioms sourceMap5301_checked
#print axioms fusedMap5301_checked
#print axioms certified5301
def sourceMap5301swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,1,0,12,13,14,15,16,9,10,11] (sourceLabel 6 6 2 v)
def fusedMap5301swap : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 6 2 v)
theorem sourceMap5301swap_checked : acceptsGraphIso
    (source (graph core5301) (root 6) 6 2) DegreeTwoThreeSpectrum6798.graph sourceMap5301swap=true := by decide +kernel
theorem fusedMap5301swap_checked : acceptsGraphIso
    (fused (graph core5301) (root 6) 6 2) DegreeTwoThreeSpectrum5048.graph fusedMap5301swap=true := by decide +kernel
theorem certified5301swap : Certified (graph core5301) (root 6) 6 2 :=
  of_native_maps core5301 DegreeTwoThreeSpectrum6798.graph DegreeTwoThreeSpectrum5048.graph
    sourceMap5301swap fusedMap5301swap sourceMap5301swap_checked fusedMap5301swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5301
#print axioms sourceMap5301swap_checked
#print axioms fusedMap5301swap_checked
#print axioms certified5301swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
