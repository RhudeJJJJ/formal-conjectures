/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons58
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2911 : Family 10 := level10.get ⟨1346,by decide⟩
def sourceMap2911 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2911 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2911_checked : acceptsGraphIso
    (source (graph core2911) (root 10) 0 4) DegreeTwoThreeSpectrum6674.graph sourceMap2911=true := by decide +kernel
theorem fusedMap2911_checked : acceptsGraphIso
    (fused (graph core2911) (root 10) 0 4) DegreeTwoThreeSpectrum6675.graph fusedMap2911=true := by decide +kernel
theorem certified2911 : Certified (graph core2911) (root 10) 0 4 :=
  of_native_maps core2911 DegreeTwoThreeSpectrum6674.graph DegreeTwoThreeSpectrum6675.graph
    sourceMap2911 fusedMap2911 sourceMap2911_checked fusedMap2911_checked
    DegreeTwoThreeFiniteComparisons.comparison2911
#print axioms sourceMap2911_checked
#print axioms fusedMap2911_checked
#print axioms certified2911
def sourceMap2911swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2911swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2911swap_checked : acceptsGraphIso
    (source (graph core2911) (root 10) 4 0) DegreeTwoThreeSpectrum6674.graph sourceMap2911swap=true := by decide +kernel
theorem fusedMap2911swap_checked : acceptsGraphIso
    (fused (graph core2911) (root 10) 4 0) DegreeTwoThreeSpectrum6675.graph fusedMap2911swap=true := by decide +kernel
theorem certified2911swap : Certified (graph core2911) (root 10) 4 0 :=
  of_native_maps core2911 DegreeTwoThreeSpectrum6674.graph DegreeTwoThreeSpectrum6675.graph
    sourceMap2911swap fusedMap2911swap sourceMap2911swap_checked fusedMap2911swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2911
#print axioms sourceMap2911swap_checked
#print axioms fusedMap2911swap_checked
#print axioms certified2911swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
