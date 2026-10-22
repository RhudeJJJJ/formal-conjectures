/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2242 : Family 9 := level9.get ⟨122,by decide⟩
def sourceMap2242 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2242 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 0 4 v)
theorem sourceMap2242_checked : acceptsGraphIso
    (source (graph core2242) (root 9) 0 4) DegreeTwoThreeSpectrum4144.graph sourceMap2242=true := by decide +kernel
theorem fusedMap2242_checked : acceptsGraphIso
    (fused (graph core2242) (root 9) 0 4) DegreeTwoThreeSpectrum4145.graph fusedMap2242=true := by decide +kernel
theorem certified2242 : Certified (graph core2242) (root 9) 0 4 :=
  of_native_maps core2242 DegreeTwoThreeSpectrum4144.graph DegreeTwoThreeSpectrum4145.graph
    sourceMap2242 fusedMap2242 sourceMap2242_checked fusedMap2242_checked
    DegreeTwoThreeFiniteComparisons.comparison2242
#print axioms sourceMap2242_checked
#print axioms fusedMap2242_checked
#print axioms certified2242
def sourceMap2242swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2242swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 4 0 v)
theorem sourceMap2242swap_checked : acceptsGraphIso
    (source (graph core2242) (root 9) 4 0) DegreeTwoThreeSpectrum4144.graph sourceMap2242swap=true := by decide +kernel
theorem fusedMap2242swap_checked : acceptsGraphIso
    (fused (graph core2242) (root 9) 4 0) DegreeTwoThreeSpectrum4145.graph fusedMap2242swap=true := by decide +kernel
theorem certified2242swap : Certified (graph core2242) (root 9) 4 0 :=
  of_native_maps core2242 DegreeTwoThreeSpectrum4144.graph DegreeTwoThreeSpectrum4145.graph
    sourceMap2242swap fusedMap2242swap sourceMap2242swap_checked fusedMap2242swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2242
#print axioms sourceMap2242swap_checked
#print axioms fusedMap2242swap_checked
#print axioms certified2242swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
