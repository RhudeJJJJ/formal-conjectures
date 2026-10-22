/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2786 : Family 10 := level10.get ⟨1042,by decide⟩
def sourceMap2786 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2786 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2786_checked : acceptsGraphIso
    (source (graph core2786) (root 10) 0 4) DegreeTwoThreeSpectrum6067.graph sourceMap2786=true := by decide +kernel
theorem fusedMap2786_checked : acceptsGraphIso
    (fused (graph core2786) (root 10) 0 4) DegreeTwoThreeSpectrum6068.graph fusedMap2786=true := by decide +kernel
theorem certified2786 : Certified (graph core2786) (root 10) 0 4 :=
  of_native_maps core2786 DegreeTwoThreeSpectrum6067.graph DegreeTwoThreeSpectrum6068.graph
    sourceMap2786 fusedMap2786 sourceMap2786_checked fusedMap2786_checked
    DegreeTwoThreeFiniteComparisons.comparison2786
#print axioms sourceMap2786_checked
#print axioms fusedMap2786_checked
#print axioms certified2786
def sourceMap2786swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2786swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2786swap_checked : acceptsGraphIso
    (source (graph core2786) (root 10) 4 0) DegreeTwoThreeSpectrum6067.graph sourceMap2786swap=true := by decide +kernel
theorem fusedMap2786swap_checked : acceptsGraphIso
    (fused (graph core2786) (root 10) 4 0) DegreeTwoThreeSpectrum6068.graph fusedMap2786swap=true := by decide +kernel
theorem certified2786swap : Certified (graph core2786) (root 10) 4 0 :=
  of_native_maps core2786 DegreeTwoThreeSpectrum6067.graph DegreeTwoThreeSpectrum6068.graph
    sourceMap2786swap fusedMap2786swap sourceMap2786swap_checked fusedMap2786swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2786
#print axioms sourceMap2786swap_checked
#print axioms fusedMap2786swap_checked
#print axioms certified2786swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
