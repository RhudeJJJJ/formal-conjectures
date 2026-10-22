/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons63
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3153 : Family 8 := level8.get ⟨60,by decide⟩
def sourceMap3153 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3153 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3153_checked : acceptsGraphIso
    (source (graph core3153) (root 8) 0 5) DegreeTwoThreeSpectrum4014.graph sourceMap3153=true := by decide +kernel
theorem fusedMap3153_checked : acceptsGraphIso
    (fused (graph core3153) (root 8) 0 5) DegreeTwoThreeSpectrum4015.graph fusedMap3153=true := by decide +kernel
theorem certified3153 : Certified (graph core3153) (root 8) 0 5 :=
  of_native_maps core3153 DegreeTwoThreeSpectrum4014.graph DegreeTwoThreeSpectrum4015.graph
    sourceMap3153 fusedMap3153 sourceMap3153_checked fusedMap3153_checked
    DegreeTwoThreeFiniteComparisons.comparison3153
#print axioms sourceMap3153_checked
#print axioms fusedMap3153_checked
#print axioms certified3153
def sourceMap3153swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,15,9] (sourceLabel 8 5 0 v)
def fusedMap3153swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3153swap_checked : acceptsGraphIso
    (source (graph core3153) (root 8) 5 0) DegreeTwoThreeSpectrum4014.graph sourceMap3153swap=true := by decide +kernel
theorem fusedMap3153swap_checked : acceptsGraphIso
    (fused (graph core3153) (root 8) 5 0) DegreeTwoThreeSpectrum4015.graph fusedMap3153swap=true := by decide +kernel
theorem certified3153swap : Certified (graph core3153) (root 8) 5 0 :=
  of_native_maps core3153 DegreeTwoThreeSpectrum4014.graph DegreeTwoThreeSpectrum4015.graph
    sourceMap3153swap fusedMap3153swap sourceMap3153swap_checked fusedMap3153swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3153
#print axioms sourceMap3153swap_checked
#print axioms fusedMap3153swap_checked
#print axioms certified3153swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
