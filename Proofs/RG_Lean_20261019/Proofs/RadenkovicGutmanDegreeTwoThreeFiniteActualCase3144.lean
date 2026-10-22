/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3144 : Family 8 := level8.get ⟨28,by decide⟩
def sourceMap3144 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,8,9,10,11,12,13] (sourceLabel 8 0 5 v)
def fusedMap3144 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3144_checked : acceptsGraphIso
    (source (graph core3144) (root 8) 0 5) DegreeTwoThreeSpectrum4149.graph sourceMap3144=true := by decide +kernel
theorem fusedMap3144_checked : acceptsGraphIso
    (fused (graph core3144) (root 8) 0 5) DegreeTwoThreeSpectrum3880.graph fusedMap3144=true := by decide +kernel
theorem certified3144 : Certified (graph core3144) (root 8) 0 5 :=
  of_native_maps core3144 DegreeTwoThreeSpectrum4149.graph DegreeTwoThreeSpectrum3880.graph
    sourceMap3144 fusedMap3144 sourceMap3144_checked fusedMap3144_checked
    DegreeTwoThreeFiniteComparisons.comparison3144
#print axioms sourceMap3144_checked
#print axioms fusedMap3144_checked
#print axioms certified3144
def sourceMap3144swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,14,8,9,10,11,12,13,15] (sourceLabel 8 5 0 v)
def fusedMap3144swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3144swap_checked : acceptsGraphIso
    (source (graph core3144) (root 8) 5 0) DegreeTwoThreeSpectrum4149.graph sourceMap3144swap=true := by decide +kernel
theorem fusedMap3144swap_checked : acceptsGraphIso
    (fused (graph core3144) (root 8) 5 0) DegreeTwoThreeSpectrum3880.graph fusedMap3144swap=true := by decide +kernel
theorem certified3144swap : Certified (graph core3144) (root 8) 5 0 :=
  of_native_maps core3144 DegreeTwoThreeSpectrum4149.graph DegreeTwoThreeSpectrum3880.graph
    sourceMap3144swap fusedMap3144swap sourceMap3144swap_checked fusedMap3144swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3144
#print axioms sourceMap3144swap_checked
#print axioms fusedMap3144swap_checked
#print axioms certified3144swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
