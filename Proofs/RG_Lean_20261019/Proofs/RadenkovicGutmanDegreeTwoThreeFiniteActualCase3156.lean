/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons63
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3156 : Family 8 := level8.get ⟨68,by decide⟩
def sourceMap3156 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3156 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3156_checked : acceptsGraphIso
    (source (graph core3156) (root 8) 0 5) DegreeTwoThreeSpectrum4050.graph sourceMap3156=true := by decide +kernel
theorem fusedMap3156_checked : acceptsGraphIso
    (fused (graph core3156) (root 8) 0 5) DegreeTwoThreeSpectrum4051.graph fusedMap3156=true := by decide +kernel
theorem certified3156 : Certified (graph core3156) (root 8) 0 5 :=
  of_native_maps core3156 DegreeTwoThreeSpectrum4050.graph DegreeTwoThreeSpectrum4051.graph
    sourceMap3156 fusedMap3156 sourceMap3156_checked fusedMap3156_checked
    DegreeTwoThreeFiniteComparisons.comparison3156
#print axioms sourceMap3156_checked
#print axioms fusedMap3156_checked
#print axioms certified3156
def sourceMap3156swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,15,9] (sourceLabel 8 5 0 v)
def fusedMap3156swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3156swap_checked : acceptsGraphIso
    (source (graph core3156) (root 8) 5 0) DegreeTwoThreeSpectrum4050.graph sourceMap3156swap=true := by decide +kernel
theorem fusedMap3156swap_checked : acceptsGraphIso
    (fused (graph core3156) (root 8) 5 0) DegreeTwoThreeSpectrum4051.graph fusedMap3156swap=true := by decide +kernel
theorem certified3156swap : Certified (graph core3156) (root 8) 5 0 :=
  of_native_maps core3156 DegreeTwoThreeSpectrum4050.graph DegreeTwoThreeSpectrum4051.graph
    sourceMap3156swap fusedMap3156swap sourceMap3156swap_checked fusedMap3156swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3156
#print axioms sourceMap3156swap_checked
#print axioms fusedMap3156swap_checked
#print axioms certified3156swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
