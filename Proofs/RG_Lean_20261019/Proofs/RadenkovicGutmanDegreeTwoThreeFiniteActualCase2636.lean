/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2636 : Family 10 := level10.get ⟨644,by decide⟩
def sourceMap2636 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2636 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2636_checked : acceptsGraphIso
    (source (graph core2636) (root 10) 0 4) DegreeTwoThreeSpectrum6409.graph sourceMap2636=true := by decide +kernel
theorem fusedMap2636_checked : acceptsGraphIso
    (fused (graph core2636) (root 10) 0 4) DegreeTwoThreeSpectrum5342.graph fusedMap2636=true := by decide +kernel
theorem certified2636 : Certified (graph core2636) (root 10) 0 4 :=
  of_native_maps core2636 DegreeTwoThreeSpectrum6409.graph DegreeTwoThreeSpectrum5342.graph
    sourceMap2636 fusedMap2636 sourceMap2636_checked fusedMap2636_checked
    DegreeTwoThreeFiniteComparisons.comparison2636
#print axioms sourceMap2636_checked
#print axioms fusedMap2636_checked
#print axioms certified2636
def sourceMap2636swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2636swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2636swap_checked : acceptsGraphIso
    (source (graph core2636) (root 10) 4 0) DegreeTwoThreeSpectrum6409.graph sourceMap2636swap=true := by decide +kernel
theorem fusedMap2636swap_checked : acceptsGraphIso
    (fused (graph core2636) (root 10) 4 0) DegreeTwoThreeSpectrum5342.graph fusedMap2636swap=true := by decide +kernel
theorem certified2636swap : Certified (graph core2636) (root 10) 4 0 :=
  of_native_maps core2636 DegreeTwoThreeSpectrum6409.graph DegreeTwoThreeSpectrum5342.graph
    sourceMap2636swap fusedMap2636swap sourceMap2636swap_checked fusedMap2636swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2636
#print axioms sourceMap2636swap_checked
#print axioms fusedMap2636swap_checked
#print axioms certified2636swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
