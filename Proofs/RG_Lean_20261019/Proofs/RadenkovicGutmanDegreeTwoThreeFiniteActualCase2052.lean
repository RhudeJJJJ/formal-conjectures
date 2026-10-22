/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2052 : Family 10 := level10.get ⟨1812,by decide⟩
def sourceMap2052 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 0 2 v)
def fusedMap2052 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2052_checked : acceptsGraphIso
    (source (graph core2052) (root 10) 0 2) DegreeTwoThreeSpectrum3747.graph sourceMap2052=true := by decide +kernel
theorem fusedMap2052_checked : acceptsGraphIso
    (fused (graph core2052) (root 10) 0 2) DegreeTwoThreeSpectrum3748.graph fusedMap2052=true := by decide +kernel
theorem certified2052 : Certified (graph core2052) (root 10) 0 2 :=
  of_native_maps core2052 DegreeTwoThreeSpectrum3747.graph DegreeTwoThreeSpectrum3748.graph
    sourceMap2052 fusedMap2052 sourceMap2052_checked fusedMap2052_checked
    DegreeTwoThreeFiniteComparisons.comparison2052
#print axioms sourceMap2052_checked
#print axioms fusedMap2052_checked
#print axioms certified2052
def sourceMap2052swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,11] (sourceLabel 10 2 0 v)
def fusedMap2052swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2052swap_checked : acceptsGraphIso
    (source (graph core2052) (root 10) 2 0) DegreeTwoThreeSpectrum3747.graph sourceMap2052swap=true := by decide +kernel
theorem fusedMap2052swap_checked : acceptsGraphIso
    (fused (graph core2052) (root 10) 2 0) DegreeTwoThreeSpectrum3748.graph fusedMap2052swap=true := by decide +kernel
theorem certified2052swap : Certified (graph core2052) (root 10) 2 0 :=
  of_native_maps core2052 DegreeTwoThreeSpectrum3747.graph DegreeTwoThreeSpectrum3748.graph
    sourceMap2052swap fusedMap2052swap sourceMap2052swap_checked fusedMap2052swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2052
#print axioms sourceMap2052swap_checked
#print axioms fusedMap2052swap_checked
#print axioms certified2052swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
