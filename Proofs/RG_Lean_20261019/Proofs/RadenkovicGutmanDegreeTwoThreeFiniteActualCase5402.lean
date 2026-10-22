/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5402 : Family 4 := level4.get ⟨6,by decide⟩
def sourceMap5402 : (Vertices 4 ⊕ Fin 5 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,6,7,8,9,1,2,3,4,5,10,11,12,13,14,15] (sourceLabel 4 4 5 v)
def fusedMap5402 : (Vertices 4 ⊕ Fin 11) → Fin 16 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 4 4 5 v)
theorem sourceMap5402_checked : acceptsGraphIso
    (source (graph core5402) (root 4) 4 5) DegreeTwoThreeSpectrum4158.graph sourceMap5402=true := by decide +kernel
theorem fusedMap5402_checked : acceptsGraphIso
    (fused (graph core5402) (root 4) 4 5) DegreeTwoThreeSpectrum3862.graph fusedMap5402=true := by decide +kernel
theorem certified5402 : Certified (graph core5402) (root 4) 4 5 :=
  of_native_maps core5402 DegreeTwoThreeSpectrum4158.graph DegreeTwoThreeSpectrum3862.graph
    sourceMap5402 fusedMap5402 sourceMap5402_checked fusedMap5402_checked
    DegreeTwoThreeFiniteComparisons.comparison5402
#print axioms sourceMap5402_checked
#print axioms fusedMap5402_checked
#print axioms certified5402
def sourceMap5402swap : (Vertices 4 ⊕ Fin 6 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,6,7,8,9,10,11,12,13,14,15,1,2,3,4,5] (sourceLabel 4 5 4 v)
def fusedMap5402swap : (Vertices 4 ⊕ Fin 11) → Fin 16 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 4 5 4 v)
theorem sourceMap5402swap_checked : acceptsGraphIso
    (source (graph core5402) (root 4) 5 4) DegreeTwoThreeSpectrum4158.graph sourceMap5402swap=true := by decide +kernel
theorem fusedMap5402swap_checked : acceptsGraphIso
    (fused (graph core5402) (root 4) 5 4) DegreeTwoThreeSpectrum3862.graph fusedMap5402swap=true := by decide +kernel
theorem certified5402swap : Certified (graph core5402) (root 4) 5 4 :=
  of_native_maps core5402 DegreeTwoThreeSpectrum4158.graph DegreeTwoThreeSpectrum3862.graph
    sourceMap5402swap fusedMap5402swap sourceMap5402swap_checked fusedMap5402swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5402
#print axioms sourceMap5402swap_checked
#print axioms fusedMap5402swap_checked
#print axioms certified5402swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
