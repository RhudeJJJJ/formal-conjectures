/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2734 : Family 10 := level10.get ⟨910,by decide⟩
def sourceMap2734 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2734 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2734_checked : acceptsGraphIso
    (source (graph core2734) (root 10) 0 4) DegreeTwoThreeSpectrum6984.graph sourceMap2734=true := by decide +kernel
theorem fusedMap2734_checked : acceptsGraphIso
    (fused (graph core2734) (root 10) 0 4) DegreeTwoThreeSpectrum5778.graph fusedMap2734=true := by decide +kernel
theorem certified2734 : Certified (graph core2734) (root 10) 0 4 :=
  of_native_maps core2734 DegreeTwoThreeSpectrum6984.graph DegreeTwoThreeSpectrum5778.graph
    sourceMap2734 fusedMap2734 sourceMap2734_checked fusedMap2734_checked
    DegreeTwoThreeFiniteComparisons.comparison2734
#print axioms sourceMap2734_checked
#print axioms fusedMap2734_checked
#print axioms certified2734
def sourceMap2734swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2734swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2734swap_checked : acceptsGraphIso
    (source (graph core2734) (root 10) 4 0) DegreeTwoThreeSpectrum6984.graph sourceMap2734swap=true := by decide +kernel
theorem fusedMap2734swap_checked : acceptsGraphIso
    (fused (graph core2734) (root 10) 4 0) DegreeTwoThreeSpectrum5778.graph fusedMap2734swap=true := by decide +kernel
theorem certified2734swap : Certified (graph core2734) (root 10) 4 0 :=
  of_native_maps core2734 DegreeTwoThreeSpectrum6984.graph DegreeTwoThreeSpectrum5778.graph
    sourceMap2734swap fusedMap2734swap sourceMap2734swap_checked fusedMap2734swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2734
#print axioms sourceMap2734swap_checked
#print axioms fusedMap2734swap_checked
#print axioms certified2734swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
