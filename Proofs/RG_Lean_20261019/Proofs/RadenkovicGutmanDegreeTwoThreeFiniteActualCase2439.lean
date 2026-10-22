/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2439 : Family 9 := level9.get ⟨639,by decide⟩
def sourceMap2439 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2439 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2439_checked : acceptsGraphIso
    (source (graph core2439) (root 9) 0 4) DegreeTwoThreeSpectrum4796.graph sourceMap2439=true := by decide +kernel
theorem fusedMap2439_checked : acceptsGraphIso
    (fused (graph core2439) (root 9) 0 4) DegreeTwoThreeSpectrum4404.graph fusedMap2439=true := by decide +kernel
theorem certified2439 : Certified (graph core2439) (root 9) 0 4 :=
  of_native_maps core2439 DegreeTwoThreeSpectrum4796.graph DegreeTwoThreeSpectrum4404.graph
    sourceMap2439 fusedMap2439 sourceMap2439_checked fusedMap2439_checked
    DegreeTwoThreeFiniteComparisons.comparison2439
#print axioms sourceMap2439_checked
#print axioms fusedMap2439_checked
#print axioms certified2439
def sourceMap2439swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2439swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2439swap_checked : acceptsGraphIso
    (source (graph core2439) (root 9) 4 0) DegreeTwoThreeSpectrum4796.graph sourceMap2439swap=true := by decide +kernel
theorem fusedMap2439swap_checked : acceptsGraphIso
    (fused (graph core2439) (root 9) 4 0) DegreeTwoThreeSpectrum4404.graph fusedMap2439swap=true := by decide +kernel
theorem certified2439swap : Certified (graph core2439) (root 9) 4 0 :=
  of_native_maps core2439 DegreeTwoThreeSpectrum4796.graph DegreeTwoThreeSpectrum4404.graph
    sourceMap2439swap fusedMap2439swap sourceMap2439swap_checked fusedMap2439swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2439
#print axioms sourceMap2439swap_checked
#print axioms fusedMap2439swap_checked
#print axioms certified2439swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
