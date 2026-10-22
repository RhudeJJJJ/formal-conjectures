/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons58
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2901 : Family 10 := level10.get ⟨1325,by decide⟩
def sourceMap2901 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2901 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2901_checked : acceptsGraphIso
    (source (graph core2901) (root 10) 0 4) DegreeTwoThreeSpectrum6633.graph sourceMap2901=true := by decide +kernel
theorem fusedMap2901_checked : acceptsGraphIso
    (fused (graph core2901) (root 10) 0 4) DegreeTwoThreeSpectrum6634.graph fusedMap2901=true := by decide +kernel
theorem certified2901 : Certified (graph core2901) (root 10) 0 4 :=
  of_native_maps core2901 DegreeTwoThreeSpectrum6633.graph DegreeTwoThreeSpectrum6634.graph
    sourceMap2901 fusedMap2901 sourceMap2901_checked fusedMap2901_checked
    DegreeTwoThreeFiniteComparisons.comparison2901
#print axioms sourceMap2901_checked
#print axioms fusedMap2901_checked
#print axioms certified2901
def sourceMap2901swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2901swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2901swap_checked : acceptsGraphIso
    (source (graph core2901) (root 10) 4 0) DegreeTwoThreeSpectrum6633.graph sourceMap2901swap=true := by decide +kernel
theorem fusedMap2901swap_checked : acceptsGraphIso
    (fused (graph core2901) (root 10) 4 0) DegreeTwoThreeSpectrum6634.graph fusedMap2901swap=true := by decide +kernel
theorem certified2901swap : Certified (graph core2901) (root 10) 4 0 :=
  of_native_maps core2901 DegreeTwoThreeSpectrum6633.graph DegreeTwoThreeSpectrum6634.graph
    sourceMap2901swap fusedMap2901swap sourceMap2901swap_checked fusedMap2901swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2901
#print axioms sourceMap2901swap_checked
#print axioms fusedMap2901swap_checked
#print axioms certified2901swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
