/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons58
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2946 : Family 10 := level10.get ⟨1429,by decide⟩
def sourceMap2946 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2946 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2946_checked : acceptsGraphIso
    (source (graph core2946) (root 10) 0 4) DegreeTwoThreeSpectrum6883.graph sourceMap2946=true := by decide +kernel
theorem fusedMap2946_checked : acceptsGraphIso
    (fused (graph core2946) (root 10) 0 4) DegreeTwoThreeSpectrum6884.graph fusedMap2946=true := by decide +kernel
theorem certified2946 : Certified (graph core2946) (root 10) 0 4 :=
  of_native_maps core2946 DegreeTwoThreeSpectrum6883.graph DegreeTwoThreeSpectrum6884.graph
    sourceMap2946 fusedMap2946 sourceMap2946_checked fusedMap2946_checked
    DegreeTwoThreeFiniteComparisons.comparison2946
#print axioms sourceMap2946_checked
#print axioms fusedMap2946_checked
#print axioms certified2946
def sourceMap2946swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2946swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2946swap_checked : acceptsGraphIso
    (source (graph core2946) (root 10) 4 0) DegreeTwoThreeSpectrum6883.graph sourceMap2946swap=true := by decide +kernel
theorem fusedMap2946swap_checked : acceptsGraphIso
    (fused (graph core2946) (root 10) 4 0) DegreeTwoThreeSpectrum6884.graph fusedMap2946swap=true := by decide +kernel
theorem certified2946swap : Certified (graph core2946) (root 10) 4 0 :=
  of_native_maps core2946 DegreeTwoThreeSpectrum6883.graph DegreeTwoThreeSpectrum6884.graph
    sourceMap2946swap fusedMap2946swap sourceMap2946swap_checked fusedMap2946swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2946
#print axioms sourceMap2946swap_checked
#print axioms fusedMap2946swap_checked
#print axioms certified2946swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
