/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2235 : Family 9 := level9.get ⟨98,by decide⟩
def sourceMap2235 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2235 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 0 4 v)
theorem sourceMap2235_checked : acceptsGraphIso
    (source (graph core2235) (root 9) 0 4) DegreeTwoThreeSpectrum4079.graph sourceMap2235=true := by decide +kernel
theorem fusedMap2235_checked : acceptsGraphIso
    (fused (graph core2235) (root 9) 0 4) DegreeTwoThreeSpectrum4080.graph fusedMap2235=true := by decide +kernel
theorem certified2235 : Certified (graph core2235) (root 9) 0 4 :=
  of_native_maps core2235 DegreeTwoThreeSpectrum4079.graph DegreeTwoThreeSpectrum4080.graph
    sourceMap2235 fusedMap2235 sourceMap2235_checked fusedMap2235_checked
    DegreeTwoThreeFiniteComparisons.comparison2235
#print axioms sourceMap2235_checked
#print axioms fusedMap2235_checked
#print axioms certified2235
def sourceMap2235swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2235swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 4 0 v)
theorem sourceMap2235swap_checked : acceptsGraphIso
    (source (graph core2235) (root 9) 4 0) DegreeTwoThreeSpectrum4079.graph sourceMap2235swap=true := by decide +kernel
theorem fusedMap2235swap_checked : acceptsGraphIso
    (fused (graph core2235) (root 9) 4 0) DegreeTwoThreeSpectrum4080.graph fusedMap2235swap=true := by decide +kernel
theorem certified2235swap : Certified (graph core2235) (root 9) 4 0 :=
  of_native_maps core2235 DegreeTwoThreeSpectrum4079.graph DegreeTwoThreeSpectrum4080.graph
    sourceMap2235swap fusedMap2235swap sourceMap2235swap_checked fusedMap2235swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2235
#print axioms sourceMap2235swap_checked
#print axioms fusedMap2235swap_checked
#print axioms certified2235swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
