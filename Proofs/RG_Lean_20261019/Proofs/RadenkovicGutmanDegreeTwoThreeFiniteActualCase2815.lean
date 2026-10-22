/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2815 : Family 10 := level10.get ⟨1117,by decide⟩
def sourceMap2815 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2815 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2815_checked : acceptsGraphIso
    (source (graph core2815) (root 10) 0 4) DegreeTwoThreeSpectrum6221.graph sourceMap2815=true := by decide +kernel
theorem fusedMap2815_checked : acceptsGraphIso
    (fused (graph core2815) (root 10) 0 4) DegreeTwoThreeSpectrum6222.graph fusedMap2815=true := by decide +kernel
theorem certified2815 : Certified (graph core2815) (root 10) 0 4 :=
  of_native_maps core2815 DegreeTwoThreeSpectrum6221.graph DegreeTwoThreeSpectrum6222.graph
    sourceMap2815 fusedMap2815 sourceMap2815_checked fusedMap2815_checked
    DegreeTwoThreeFiniteComparisons.comparison2815
#print axioms sourceMap2815_checked
#print axioms fusedMap2815_checked
#print axioms certified2815
def sourceMap2815swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2815swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2815swap_checked : acceptsGraphIso
    (source (graph core2815) (root 10) 4 0) DegreeTwoThreeSpectrum6221.graph sourceMap2815swap=true := by decide +kernel
theorem fusedMap2815swap_checked : acceptsGraphIso
    (fused (graph core2815) (root 10) 4 0) DegreeTwoThreeSpectrum6222.graph fusedMap2815swap=true := by decide +kernel
theorem certified2815swap : Certified (graph core2815) (root 10) 4 0 :=
  of_native_maps core2815 DegreeTwoThreeSpectrum6221.graph DegreeTwoThreeSpectrum6222.graph
    sourceMap2815swap fusedMap2815swap sourceMap2815swap_checked fusedMap2815swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2815
#print axioms sourceMap2815swap_checked
#print axioms fusedMap2815swap_checked
#print axioms certified2815swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
