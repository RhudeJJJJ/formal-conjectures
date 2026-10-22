/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2887 : Family 10 := level10.get ⟨1288,by decide⟩
def sourceMap2887 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2887 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2887_checked : acceptsGraphIso
    (source (graph core2887) (root 10) 0 4) DegreeTwoThreeSpectrum6560.graph sourceMap2887=true := by decide +kernel
theorem fusedMap2887_checked : acceptsGraphIso
    (fused (graph core2887) (root 10) 0 4) DegreeTwoThreeSpectrum6561.graph fusedMap2887=true := by decide +kernel
theorem certified2887 : Certified (graph core2887) (root 10) 0 4 :=
  of_native_maps core2887 DegreeTwoThreeSpectrum6560.graph DegreeTwoThreeSpectrum6561.graph
    sourceMap2887 fusedMap2887 sourceMap2887_checked fusedMap2887_checked
    DegreeTwoThreeFiniteComparisons.comparison2887
#print axioms sourceMap2887_checked
#print axioms fusedMap2887_checked
#print axioms certified2887
def sourceMap2887swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2887swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2887swap_checked : acceptsGraphIso
    (source (graph core2887) (root 10) 4 0) DegreeTwoThreeSpectrum6560.graph sourceMap2887swap=true := by decide +kernel
theorem fusedMap2887swap_checked : acceptsGraphIso
    (fused (graph core2887) (root 10) 4 0) DegreeTwoThreeSpectrum6561.graph fusedMap2887swap=true := by decide +kernel
theorem certified2887swap : Certified (graph core2887) (root 10) 4 0 :=
  of_native_maps core2887 DegreeTwoThreeSpectrum6560.graph DegreeTwoThreeSpectrum6561.graph
    sourceMap2887swap fusedMap2887swap sourceMap2887swap_checked fusedMap2887swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2887
#print axioms sourceMap2887swap_checked
#print axioms fusedMap2887swap_checked
#print axioms certified2887swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
