/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2543 : Family 10 := level10.get ⟨360,by decide⟩
def sourceMap2543 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2543 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2543_checked : acceptsGraphIso
    (source (graph core2543) (root 10) 0 4) DegreeTwoThreeSpectrum5641.graph sourceMap2543=true := by decide +kernel
theorem fusedMap2543_checked : acceptsGraphIso
    (fused (graph core2543) (root 10) 0 4) DegreeTwoThreeSpectrum5642.graph fusedMap2543=true := by decide +kernel
theorem certified2543 : Certified (graph core2543) (root 10) 0 4 :=
  of_native_maps core2543 DegreeTwoThreeSpectrum5641.graph DegreeTwoThreeSpectrum5642.graph
    sourceMap2543 fusedMap2543 sourceMap2543_checked fusedMap2543_checked
    DegreeTwoThreeFiniteComparisons.comparison2543
#print axioms sourceMap2543_checked
#print axioms fusedMap2543_checked
#print axioms certified2543
def sourceMap2543swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2543swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2543swap_checked : acceptsGraphIso
    (source (graph core2543) (root 10) 4 0) DegreeTwoThreeSpectrum5641.graph sourceMap2543swap=true := by decide +kernel
theorem fusedMap2543swap_checked : acceptsGraphIso
    (fused (graph core2543) (root 10) 4 0) DegreeTwoThreeSpectrum5642.graph fusedMap2543swap=true := by decide +kernel
theorem certified2543swap : Certified (graph core2543) (root 10) 4 0 :=
  of_native_maps core2543 DegreeTwoThreeSpectrum5641.graph DegreeTwoThreeSpectrum5642.graph
    sourceMap2543swap fusedMap2543swap sourceMap2543swap_checked fusedMap2543swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2543
#print axioms sourceMap2543swap_checked
#print axioms fusedMap2543swap_checked
#print axioms certified2543swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
