/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2233 : Family 9 := level9.get ⟨90,by decide⟩
def sourceMap2233 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2233 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 0 4 v)
theorem sourceMap2233_checked : acceptsGraphIso
    (source (graph core2233) (root 9) 0 4) DegreeTwoThreeSpectrum4053.graph sourceMap2233=true := by decide +kernel
theorem fusedMap2233_checked : acceptsGraphIso
    (fused (graph core2233) (root 9) 0 4) DegreeTwoThreeSpectrum4054.graph fusedMap2233=true := by decide +kernel
theorem certified2233 : Certified (graph core2233) (root 9) 0 4 :=
  of_native_maps core2233 DegreeTwoThreeSpectrum4053.graph DegreeTwoThreeSpectrum4054.graph
    sourceMap2233 fusedMap2233 sourceMap2233_checked fusedMap2233_checked
    DegreeTwoThreeFiniteComparisons.comparison2233
#print axioms sourceMap2233_checked
#print axioms fusedMap2233_checked
#print axioms certified2233
def sourceMap2233swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2233swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 4 0 v)
theorem sourceMap2233swap_checked : acceptsGraphIso
    (source (graph core2233) (root 9) 4 0) DegreeTwoThreeSpectrum4053.graph sourceMap2233swap=true := by decide +kernel
theorem fusedMap2233swap_checked : acceptsGraphIso
    (fused (graph core2233) (root 9) 4 0) DegreeTwoThreeSpectrum4054.graph fusedMap2233swap=true := by decide +kernel
theorem certified2233swap : Certified (graph core2233) (root 9) 4 0 :=
  of_native_maps core2233 DegreeTwoThreeSpectrum4053.graph DegreeTwoThreeSpectrum4054.graph
    sourceMap2233swap fusedMap2233swap sourceMap2233swap_checked fusedMap2233swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2233
#print axioms sourceMap2233swap_checked
#print axioms fusedMap2233swap_checked
#print axioms certified2233swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
