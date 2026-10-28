/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5243 : Family 7 := level7.get ⟨11,by decide⟩
def sourceMap5243 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,10,7,8,9,11,12,13,14,15,16] (sourceLabel 7 2 5 v)
def fusedMap5243 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 2 5 v)
theorem sourceMap5243_checked : acceptsGraphIso
    (source (graph core5243) (root 7) 2 5) DegreeTwoThreeSpectrum5399.graph sourceMap5243=true := by decide +kernel
theorem fusedMap5243_checked : acceptsGraphIso
    (fused (graph core5243) (root 7) 2 5) DegreeTwoThreeSpectrum4998.graph fusedMap5243=true := by decide +kernel
theorem certified5243 : Certified (graph core5243) (root 7) 2 5 :=
  of_native_maps core5243 DegreeTwoThreeSpectrum5399.graph DegreeTwoThreeSpectrum4998.graph
    sourceMap5243 fusedMap5243 sourceMap5243_checked fusedMap5243_checked
    DegreeTwoThreeFiniteComparisons.comparison5243
#print axioms sourceMap5243_checked
#print axioms fusedMap5243_checked
#print axioms certified5243
def sourceMap5243swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,14,15,16,7,8,9] (sourceLabel 7 5 2 v)
def fusedMap5243swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 5 2 v)
theorem sourceMap5243swap_checked : acceptsGraphIso
    (source (graph core5243) (root 7) 5 2) DegreeTwoThreeSpectrum5399.graph sourceMap5243swap=true := by decide +kernel
theorem fusedMap5243swap_checked : acceptsGraphIso
    (fused (graph core5243) (root 7) 5 2) DegreeTwoThreeSpectrum4998.graph fusedMap5243swap=true := by decide +kernel
theorem certified5243swap : Certified (graph core5243) (root 7) 5 2 :=
  of_native_maps core5243 DegreeTwoThreeSpectrum5399.graph DegreeTwoThreeSpectrum4998.graph
    sourceMap5243swap fusedMap5243swap sourceMap5243swap_checked fusedMap5243swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5243
#print axioms sourceMap5243swap_checked
#print axioms fusedMap5243swap_checked
#print axioms certified5243swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
