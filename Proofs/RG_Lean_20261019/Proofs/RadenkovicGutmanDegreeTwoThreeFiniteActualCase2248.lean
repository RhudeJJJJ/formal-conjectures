/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2248 : Family 9 := level9.get ⟨134,by decide⟩
def sourceMap2248 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,10,11,12,13,14,15,6,7,8,9,1,2,3,4,5] (sourceLabel 9 0 4 v)
def fusedMap2248 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,13,14,15,7,8,9,10,11,12] (fusedLabel 9 0 4 v)
theorem sourceMap2248_checked : acceptsGraphIso
    (source (graph core2248) (root 9) 0 4) DegreeTwoThreeSpectrum4156.graph sourceMap2248=true := by decide +kernel
theorem fusedMap2248_checked : acceptsGraphIso
    (fused (graph core2248) (root 9) 0 4) DegreeTwoThreeSpectrum4169.graph fusedMap2248=true := by decide +kernel
theorem certified2248 : Certified (graph core2248) (root 9) 0 4 :=
  of_native_maps core2248 DegreeTwoThreeSpectrum4156.graph DegreeTwoThreeSpectrum4169.graph
    sourceMap2248 fusedMap2248 sourceMap2248_checked fusedMap2248_checked
    DegreeTwoThreeFiniteComparisons.comparison2248
#print axioms sourceMap2248_checked
#print axioms fusedMap2248_checked
#print axioms certified2248
def sourceMap2248swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,10,11,12,13,14,15,6,7,8,1,2,3,4,5,9] (sourceLabel 9 4 0 v)
def fusedMap2248swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,13,14,15,7,8,9,10,11,12] (fusedLabel 9 4 0 v)
theorem sourceMap2248swap_checked : acceptsGraphIso
    (source (graph core2248) (root 9) 4 0) DegreeTwoThreeSpectrum4156.graph sourceMap2248swap=true := by decide +kernel
theorem fusedMap2248swap_checked : acceptsGraphIso
    (fused (graph core2248) (root 9) 4 0) DegreeTwoThreeSpectrum4169.graph fusedMap2248swap=true := by decide +kernel
theorem certified2248swap : Certified (graph core2248) (root 9) 4 0 :=
  of_native_maps core2248 DegreeTwoThreeSpectrum4156.graph DegreeTwoThreeSpectrum4169.graph
    sourceMap2248swap fusedMap2248swap sourceMap2248swap_checked fusedMap2248swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2248
#print axioms sourceMap2248swap_checked
#print axioms fusedMap2248swap_checked
#print axioms certified2248swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
