/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5423 : Family 3 := level3.get ⟨2,by decide⟩
def sourceMap5423 : (Vertices 3 ⊕ Fin 6 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,7,8,9,1,2,3,4,5,6,10,11,12,13,14,15,16] (sourceLabel 3 5 6 v)
def fusedMap5423 : (Vertices 3 ⊕ Fin 13) → Fin 17 :=
  fun v => ![5,6,7,8,4,3,2,1,0,9,10,11,12,13,14,15,16] (fusedLabel 3 5 6 v)
theorem sourceMap5423_checked : acceptsGraphIso
    (source (graph core5423) (root 3) 5 6) DegreeTwoThreeSpectrum5126.graph sourceMap5423=true := by decide +kernel
theorem fusedMap5423_checked : acceptsGraphIso
    (fused (graph core5423) (root 3) 5 6) DegreeTwoThreeSpectrum4960.graph fusedMap5423=true := by decide +kernel
theorem certified5423 : Certified (graph core5423) (root 3) 5 6 :=
  of_native_maps core5423 DegreeTwoThreeSpectrum5126.graph DegreeTwoThreeSpectrum4960.graph
    sourceMap5423 fusedMap5423 sourceMap5423_checked fusedMap5423_checked
    DegreeTwoThreeFiniteComparisons.comparison5423
#print axioms sourceMap5423_checked
#print axioms fusedMap5423_checked
#print axioms certified5423
def sourceMap5423swap : (Vertices 3 ⊕ Fin 7 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,7,8,9,10,11,12,13,14,15,16,1,2,3,4,5,6] (sourceLabel 3 6 5 v)
def fusedMap5423swap : (Vertices 3 ⊕ Fin 13) → Fin 17 :=
  fun v => ![5,6,7,8,4,3,2,1,0,9,10,11,12,13,14,15,16] (fusedLabel 3 6 5 v)
theorem sourceMap5423swap_checked : acceptsGraphIso
    (source (graph core5423) (root 3) 6 5) DegreeTwoThreeSpectrum5126.graph sourceMap5423swap=true := by decide +kernel
theorem fusedMap5423swap_checked : acceptsGraphIso
    (fused (graph core5423) (root 3) 6 5) DegreeTwoThreeSpectrum4960.graph fusedMap5423swap=true := by decide +kernel
theorem certified5423swap : Certified (graph core5423) (root 3) 6 5 :=
  of_native_maps core5423 DegreeTwoThreeSpectrum5126.graph DegreeTwoThreeSpectrum4960.graph
    sourceMap5423swap fusedMap5423swap sourceMap5423swap_checked fusedMap5423swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5423
#print axioms sourceMap5423swap_checked
#print axioms fusedMap5423swap_checked
#print axioms certified5423swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
