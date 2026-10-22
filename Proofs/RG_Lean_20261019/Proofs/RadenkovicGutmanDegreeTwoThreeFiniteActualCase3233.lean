/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3233 : Family 8 := level8.get ⟨266,by decide⟩
def sourceMap3233 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3233 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3233_checked : acceptsGraphIso
    (source (graph core3233) (root 8) 0 5) DegreeTwoThreeSpectrum4673.graph sourceMap3233=true := by decide +kernel
theorem fusedMap3233_checked : acceptsGraphIso
    (fused (graph core3233) (root 8) 0 5) DegreeTwoThreeSpectrum4173.graph fusedMap3233=true := by decide +kernel
theorem certified3233 : Certified (graph core3233) (root 8) 0 5 :=
  of_native_maps core3233 DegreeTwoThreeSpectrum4673.graph DegreeTwoThreeSpectrum4173.graph
    sourceMap3233 fusedMap3233 sourceMap3233_checked fusedMap3233_checked
    DegreeTwoThreeFiniteComparisons.comparison3233
#print axioms sourceMap3233_checked
#print axioms fusedMap3233_checked
#print axioms certified3233
def sourceMap3233swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,12,13,14,15,11] (sourceLabel 8 5 0 v)
def fusedMap3233swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3233swap_checked : acceptsGraphIso
    (source (graph core3233) (root 8) 5 0) DegreeTwoThreeSpectrum4673.graph sourceMap3233swap=true := by decide +kernel
theorem fusedMap3233swap_checked : acceptsGraphIso
    (fused (graph core3233) (root 8) 5 0) DegreeTwoThreeSpectrum4173.graph fusedMap3233swap=true := by decide +kernel
theorem certified3233swap : Certified (graph core3233) (root 8) 5 0 :=
  of_native_maps core3233 DegreeTwoThreeSpectrum4673.graph DegreeTwoThreeSpectrum4173.graph
    sourceMap3233swap fusedMap3233swap sourceMap3233swap_checked fusedMap3233swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3233
#print axioms sourceMap3233swap_checked
#print axioms fusedMap3233swap_checked
#print axioms certified3233swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
