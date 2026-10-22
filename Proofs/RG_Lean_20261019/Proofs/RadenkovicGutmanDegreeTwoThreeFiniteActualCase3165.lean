/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons63
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3165 : Family 8 := level8.get ⟨92,by decide⟩
def sourceMap3165 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3165 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3165_checked : acceptsGraphIso
    (source (graph core3165) (root 8) 0 5) DegreeTwoThreeSpectrum4156.graph sourceMap3165=true := by decide +kernel
theorem fusedMap3165_checked : acceptsGraphIso
    (fused (graph core3165) (root 8) 0 5) DegreeTwoThreeSpectrum4157.graph fusedMap3165=true := by decide +kernel
theorem certified3165 : Certified (graph core3165) (root 8) 0 5 :=
  of_native_maps core3165 DegreeTwoThreeSpectrum4156.graph DegreeTwoThreeSpectrum4157.graph
    sourceMap3165 fusedMap3165 sourceMap3165_checked fusedMap3165_checked
    DegreeTwoThreeFiniteComparisons.comparison3165
#print axioms sourceMap3165_checked
#print axioms fusedMap3165_checked
#print axioms certified3165
def sourceMap3165swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,15,9] (sourceLabel 8 5 0 v)
def fusedMap3165swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3165swap_checked : acceptsGraphIso
    (source (graph core3165) (root 8) 5 0) DegreeTwoThreeSpectrum4156.graph sourceMap3165swap=true := by decide +kernel
theorem fusedMap3165swap_checked : acceptsGraphIso
    (fused (graph core3165) (root 8) 5 0) DegreeTwoThreeSpectrum4157.graph fusedMap3165swap=true := by decide +kernel
theorem certified3165swap : Certified (graph core3165) (root 8) 5 0 :=
  of_native_maps core3165 DegreeTwoThreeSpectrum4156.graph DegreeTwoThreeSpectrum4157.graph
    sourceMap3165swap fusedMap3165swap sourceMap3165swap_checked fusedMap3165swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3165
#print axioms sourceMap3165swap_checked
#print axioms fusedMap3165swap_checked
#print axioms certified3165swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
