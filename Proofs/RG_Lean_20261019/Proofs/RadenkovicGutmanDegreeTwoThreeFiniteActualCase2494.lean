/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2494 : Family 10 := level10.get ⟨183,by decide⟩
def sourceMap2494 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,7,8,9,2,3,4,5,6] (sourceLabel 10 0 4 v)
def fusedMap2494 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,9,10,11,12,13,14,15,16,7,8,1,2,3,4,5,6] (fusedLabel 10 0 4 v)
theorem sourceMap2494_checked : acceptsGraphIso
    (source (graph core2494) (root 10) 0 4) DegreeTwoThreeSpectrum5940.graph sourceMap2494=true := by decide +kernel
theorem fusedMap2494_checked : acceptsGraphIso
    (fused (graph core2494) (root 10) 0 4) DegreeTwoThreeSpectrum5127.graph fusedMap2494=true := by decide +kernel
theorem certified2494 : Certified (graph core2494) (root 10) 0 4 :=
  of_native_maps core2494 DegreeTwoThreeSpectrum5940.graph DegreeTwoThreeSpectrum5127.graph
    sourceMap2494 fusedMap2494 sourceMap2494_checked fusedMap2494_checked
    DegreeTwoThreeFiniteComparisons.comparison2494
#print axioms sourceMap2494_checked
#print axioms fusedMap2494_checked
#print axioms certified2494
def sourceMap2494swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,7,8,2,3,4,5,6,9] (sourceLabel 10 4 0 v)
def fusedMap2494swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,9,10,11,12,13,14,15,16,7,8,1,2,3,4,5,6] (fusedLabel 10 4 0 v)
theorem sourceMap2494swap_checked : acceptsGraphIso
    (source (graph core2494) (root 10) 4 0) DegreeTwoThreeSpectrum5940.graph sourceMap2494swap=true := by decide +kernel
theorem fusedMap2494swap_checked : acceptsGraphIso
    (fused (graph core2494) (root 10) 4 0) DegreeTwoThreeSpectrum5127.graph fusedMap2494swap=true := by decide +kernel
theorem certified2494swap : Certified (graph core2494) (root 10) 4 0 :=
  of_native_maps core2494 DegreeTwoThreeSpectrum5940.graph DegreeTwoThreeSpectrum5127.graph
    sourceMap2494swap fusedMap2494swap sourceMap2494swap_checked fusedMap2494swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2494
#print axioms sourceMap2494swap_checked
#print axioms fusedMap2494swap_checked
#print axioms certified2494swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
