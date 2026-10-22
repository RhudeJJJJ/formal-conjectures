/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2009 : Family 10 := level10.get ⟨1641,by decide⟩
def sourceMap2009 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,14,7,8,9] (sourceLabel 10 0 2 v)
def fusedMap2009 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2009_checked : acceptsGraphIso
    (source (graph core2009) (root 10) 0 2) DegreeTwoThreeSpectrum3797.graph sourceMap2009=true := by decide +kernel
theorem fusedMap2009_checked : acceptsGraphIso
    (fused (graph core2009) (root 10) 0 2) DegreeTwoThreeSpectrum3190.graph fusedMap2009=true := by decide +kernel
theorem certified2009 : Certified (graph core2009) (root 10) 0 2 :=
  of_native_maps core2009 DegreeTwoThreeSpectrum3797.graph DegreeTwoThreeSpectrum3190.graph
    sourceMap2009 fusedMap2009 sourceMap2009_checked fusedMap2009_checked
    DegreeTwoThreeFiniteComparisons.comparison2009
#print axioms sourceMap2009_checked
#print axioms fusedMap2009_checked
#print axioms certified2009
def sourceMap2009swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,7,8,9,14] (sourceLabel 10 2 0 v)
def fusedMap2009swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2009swap_checked : acceptsGraphIso
    (source (graph core2009) (root 10) 2 0) DegreeTwoThreeSpectrum3797.graph sourceMap2009swap=true := by decide +kernel
theorem fusedMap2009swap_checked : acceptsGraphIso
    (fused (graph core2009) (root 10) 2 0) DegreeTwoThreeSpectrum3190.graph fusedMap2009swap=true := by decide +kernel
theorem certified2009swap : Certified (graph core2009) (root 10) 2 0 :=
  of_native_maps core2009 DegreeTwoThreeSpectrum3797.graph DegreeTwoThreeSpectrum3190.graph
    sourceMap2009swap fusedMap2009swap sourceMap2009swap_checked fusedMap2009swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2009
#print axioms sourceMap2009swap_checked
#print axioms fusedMap2009swap_checked
#print axioms certified2009swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
