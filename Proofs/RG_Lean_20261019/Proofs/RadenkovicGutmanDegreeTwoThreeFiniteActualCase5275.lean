/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5275 : Family 7 := level7.get ⟨95,by decide⟩
def sourceMap5275 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,8,9,10,11,5,6,7,0,12,13,14,15,16] (sourceLabel 7 2 5 v)
def fusedMap5275 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 2 5 v)
theorem sourceMap5275_checked : acceptsGraphIso
    (source (graph core5275) (root 7) 2 5) DegreeTwoThreeSpectrum6799.graph sourceMap5275=true := by decide +kernel
theorem fusedMap5275_checked : acceptsGraphIso
    (fused (graph core5275) (root 7) 2 5) DegreeTwoThreeSpectrum5675.graph fusedMap5275=true := by decide +kernel
theorem certified5275 : Certified (graph core5275) (root 7) 2 5 :=
  of_native_maps core5275 DegreeTwoThreeSpectrum6799.graph DegreeTwoThreeSpectrum5675.graph
    sourceMap5275 fusedMap5275 sourceMap5275_checked fusedMap5275_checked
    DegreeTwoThreeFiniteComparisons.comparison5275
#print axioms sourceMap5275_checked
#print axioms fusedMap5275_checked
#print axioms certified5275
def sourceMap5275swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,8,9,10,11,0,12,13,14,15,16,5,6,7] (sourceLabel 7 5 2 v)
def fusedMap5275swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 5 2 v)
theorem sourceMap5275swap_checked : acceptsGraphIso
    (source (graph core5275) (root 7) 5 2) DegreeTwoThreeSpectrum6799.graph sourceMap5275swap=true := by decide +kernel
theorem fusedMap5275swap_checked : acceptsGraphIso
    (fused (graph core5275) (root 7) 5 2) DegreeTwoThreeSpectrum5675.graph fusedMap5275swap=true := by decide +kernel
theorem certified5275swap : Certified (graph core5275) (root 7) 5 2 :=
  of_native_maps core5275 DegreeTwoThreeSpectrum6799.graph DegreeTwoThreeSpectrum5675.graph
    sourceMap5275swap fusedMap5275swap sourceMap5275swap_checked fusedMap5275swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5275
#print axioms sourceMap5275swap_checked
#print axioms fusedMap5275swap_checked
#print axioms certified5275swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
