/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5407 : Family 5 := level5.get ⟨14,by decide⟩
def sourceMap5407 : (Vertices 5 ⊕ Fin 5 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,6,7,8,9,10,1,2,3,4,5,11,12,13,14,15,16] (sourceLabel 5 4 5 v)
def fusedMap5407 : (Vertices 5 ⊕ Fin 11) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 5 4 5 v)
theorem sourceMap5407_checked : acceptsGraphIso
    (source (graph core5407) (root 5) 4 5) DegreeTwoThreeSpectrum5929.graph sourceMap5407=true := by decide +kernel
theorem fusedMap5407_checked : acceptsGraphIso
    (fused (graph core5407) (root 5) 4 5) DegreeTwoThreeSpectrum4966.graph fusedMap5407=true := by decide +kernel
theorem certified5407 : Certified (graph core5407) (root 5) 4 5 :=
  of_native_maps core5407 DegreeTwoThreeSpectrum5929.graph DegreeTwoThreeSpectrum4966.graph
    sourceMap5407 fusedMap5407 sourceMap5407_checked fusedMap5407_checked
    DegreeTwoThreeFiniteComparisons.comparison5407
#print axioms sourceMap5407_checked
#print axioms fusedMap5407_checked
#print axioms certified5407
def sourceMap5407swap : (Vertices 5 ⊕ Fin 6 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,6,7,8,9,10,11,12,13,14,15,16,1,2,3,4,5] (sourceLabel 5 5 4 v)
def fusedMap5407swap : (Vertices 5 ⊕ Fin 11) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 5 5 4 v)
theorem sourceMap5407swap_checked : acceptsGraphIso
    (source (graph core5407) (root 5) 5 4) DegreeTwoThreeSpectrum5929.graph sourceMap5407swap=true := by decide +kernel
theorem fusedMap5407swap_checked : acceptsGraphIso
    (fused (graph core5407) (root 5) 5 4) DegreeTwoThreeSpectrum4966.graph fusedMap5407swap=true := by decide +kernel
theorem certified5407swap : Certified (graph core5407) (root 5) 5 4 :=
  of_native_maps core5407 DegreeTwoThreeSpectrum5929.graph DegreeTwoThreeSpectrum4966.graph
    sourceMap5407swap fusedMap5407swap sourceMap5407swap_checked fusedMap5407swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5407
#print axioms sourceMap5407swap_checked
#print axioms fusedMap5407swap_checked
#print axioms certified5407swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
