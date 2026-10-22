/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2510 : Family 10 := level10.get ⟨249,by decide⟩
def sourceMap2510 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2510 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2510_checked : acceptsGraphIso
    (source (graph core2510) (root 10) 0 4) DegreeTwoThreeSpectrum5337.graph sourceMap2510=true := by decide +kernel
theorem fusedMap2510_checked : acceptsGraphIso
    (fused (graph core2510) (root 10) 0 4) DegreeTwoThreeSpectrum5338.graph fusedMap2510=true := by decide +kernel
theorem certified2510 : Certified (graph core2510) (root 10) 0 4 :=
  of_native_maps core2510 DegreeTwoThreeSpectrum5337.graph DegreeTwoThreeSpectrum5338.graph
    sourceMap2510 fusedMap2510 sourceMap2510_checked fusedMap2510_checked
    DegreeTwoThreeFiniteComparisons.comparison2510
#print axioms sourceMap2510_checked
#print axioms fusedMap2510_checked
#print axioms certified2510
def sourceMap2510swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2510swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2510swap_checked : acceptsGraphIso
    (source (graph core2510) (root 10) 4 0) DegreeTwoThreeSpectrum5337.graph sourceMap2510swap=true := by decide +kernel
theorem fusedMap2510swap_checked : acceptsGraphIso
    (fused (graph core2510) (root 10) 4 0) DegreeTwoThreeSpectrum5338.graph fusedMap2510swap=true := by decide +kernel
theorem certified2510swap : Certified (graph core2510) (root 10) 4 0 :=
  of_native_maps core2510 DegreeTwoThreeSpectrum5337.graph DegreeTwoThreeSpectrum5338.graph
    sourceMap2510swap fusedMap2510swap sourceMap2510swap_checked fusedMap2510swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2510
#print axioms sourceMap2510swap_checked
#print axioms fusedMap2510swap_checked
#print axioms certified2510swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
