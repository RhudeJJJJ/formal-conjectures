/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5091 : Family 7 := level7.get ⟨37,by decide⟩
def sourceMap5091 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,9,10,6,7,8,11,12,13,14,15] (sourceLabel 7 2 4 v)
def fusedMap5091 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 2 4 v)
theorem sourceMap5091_checked : acceptsGraphIso
    (source (graph core5091) (root 7) 2 4) DegreeTwoThreeSpectrum4374.graph sourceMap5091=true := by decide +kernel
theorem fusedMap5091_checked : acceptsGraphIso
    (fused (graph core5091) (root 7) 2 4) DegreeTwoThreeSpectrum3963.graph fusedMap5091=true := by decide +kernel
theorem certified5091 : Certified (graph core5091) (root 7) 2 4 :=
  of_native_maps core5091 DegreeTwoThreeSpectrum4374.graph DegreeTwoThreeSpectrum3963.graph
    sourceMap5091 fusedMap5091 sourceMap5091_checked fusedMap5091_checked
    DegreeTwoThreeFiniteComparisons.comparison5091
#print axioms sourceMap5091_checked
#print axioms fusedMap5091_checked
#print axioms certified5091
def sourceMap5091swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,9,10,11,12,13,14,15,6,7,8] (sourceLabel 7 4 2 v)
def fusedMap5091swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 4 2 v)
theorem sourceMap5091swap_checked : acceptsGraphIso
    (source (graph core5091) (root 7) 4 2) DegreeTwoThreeSpectrum4374.graph sourceMap5091swap=true := by decide +kernel
theorem fusedMap5091swap_checked : acceptsGraphIso
    (fused (graph core5091) (root 7) 4 2) DegreeTwoThreeSpectrum3963.graph fusedMap5091swap=true := by decide +kernel
theorem certified5091swap : Certified (graph core5091) (root 7) 4 2 :=
  of_native_maps core5091 DegreeTwoThreeSpectrum4374.graph DegreeTwoThreeSpectrum3963.graph
    sourceMap5091swap fusedMap5091swap sourceMap5091swap_checked fusedMap5091swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5091
#print axioms sourceMap5091swap_checked
#print axioms fusedMap5091swap_checked
#print axioms certified5091swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
