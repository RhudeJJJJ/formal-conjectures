/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5345 : Family 6 := level6.get ⟨30,by decide⟩
def sourceMap5345 : (Vertices 6 ⊕ Fin 4 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,5,6,7,8,9,10,1,2,3,4,11,12,13,14,15] (sourceLabel 6 3 4 v)
def fusedMap5345 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 3 4 v)
theorem sourceMap5345_checked : acceptsGraphIso
    (source (graph core5345) (root 6) 3 4) DegreeTwoThreeSpectrum4636.graph sourceMap5345=true := by decide +kernel
theorem fusedMap5345_checked : acceptsGraphIso
    (fused (graph core5345) (root 6) 3 4) DegreeTwoThreeSpectrum4008.graph fusedMap5345=true := by decide +kernel
theorem certified5345 : Certified (graph core5345) (root 6) 3 4 :=
  of_native_maps core5345 DegreeTwoThreeSpectrum4636.graph DegreeTwoThreeSpectrum4008.graph
    sourceMap5345 fusedMap5345 sourceMap5345_checked fusedMap5345_checked
    DegreeTwoThreeFiniteComparisons.comparison5345
#print axioms sourceMap5345_checked
#print axioms fusedMap5345_checked
#print axioms certified5345
def sourceMap5345swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 4) → Fin 16 :=
  fun v => ![0,5,6,7,8,9,10,11,12,13,14,15,1,2,3,4] (sourceLabel 6 4 3 v)
def fusedMap5345swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 4 3 v)
theorem sourceMap5345swap_checked : acceptsGraphIso
    (source (graph core5345) (root 6) 4 3) DegreeTwoThreeSpectrum4636.graph sourceMap5345swap=true := by decide +kernel
theorem fusedMap5345swap_checked : acceptsGraphIso
    (fused (graph core5345) (root 6) 4 3) DegreeTwoThreeSpectrum4008.graph fusedMap5345swap=true := by decide +kernel
theorem certified5345swap : Certified (graph core5345) (root 6) 4 3 :=
  of_native_maps core5345 DegreeTwoThreeSpectrum4636.graph DegreeTwoThreeSpectrum4008.graph
    sourceMap5345swap fusedMap5345swap sourceMap5345swap_checked fusedMap5345swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5345
#print axioms sourceMap5345swap_checked
#print axioms fusedMap5345swap_checked
#print axioms certified5345swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
