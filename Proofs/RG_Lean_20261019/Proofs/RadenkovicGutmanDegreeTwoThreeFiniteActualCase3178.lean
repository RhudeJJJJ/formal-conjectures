/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons63
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3178 : Family 8 := level8.get ⟨129,by decide⟩
def sourceMap3178 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3178 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3178_checked : acceptsGraphIso
    (source (graph core3178) (root 8) 0 5) DegreeTwoThreeSpectrum4379.graph sourceMap3178=true := by decide +kernel
theorem fusedMap3178_checked : acceptsGraphIso
    (fused (graph core3178) (root 8) 0 5) DegreeTwoThreeSpectrum3960.graph fusedMap3178=true := by decide +kernel
theorem certified3178 : Certified (graph core3178) (root 8) 0 5 :=
  of_native_maps core3178 DegreeTwoThreeSpectrum4379.graph DegreeTwoThreeSpectrum3960.graph
    sourceMap3178 fusedMap3178 sourceMap3178_checked fusedMap3178_checked
    DegreeTwoThreeFiniteComparisons.comparison3178
#print axioms sourceMap3178_checked
#print axioms fusedMap3178_checked
#print axioms certified3178
def sourceMap3178swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3178swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3178swap_checked : acceptsGraphIso
    (source (graph core3178) (root 8) 5 0) DegreeTwoThreeSpectrum4379.graph sourceMap3178swap=true := by decide +kernel
theorem fusedMap3178swap_checked : acceptsGraphIso
    (fused (graph core3178) (root 8) 5 0) DegreeTwoThreeSpectrum3960.graph fusedMap3178swap=true := by decide +kernel
theorem certified3178swap : Certified (graph core3178) (root 8) 5 0 :=
  of_native_maps core3178 DegreeTwoThreeSpectrum4379.graph DegreeTwoThreeSpectrum3960.graph
    sourceMap3178swap fusedMap3178swap sourceMap3178swap_checked fusedMap3178swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3178
#print axioms sourceMap3178swap_checked
#print axioms fusedMap3178swap_checked
#print axioms certified3178swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
