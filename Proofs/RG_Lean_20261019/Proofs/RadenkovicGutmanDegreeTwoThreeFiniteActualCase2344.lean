/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2344 : Family 9 := level9.get ⟨407,by decide⟩
def sourceMap2344 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2344 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2344_checked : acceptsGraphIso
    (source (graph core2344) (root 9) 0 4) DegreeTwoThreeSpectrum4370.graph sourceMap2344=true := by decide +kernel
theorem fusedMap2344_checked : acceptsGraphIso
    (fused (graph core2344) (root 9) 0 4) DegreeTwoThreeSpectrum4371.graph fusedMap2344=true := by decide +kernel
theorem certified2344 : Certified (graph core2344) (root 9) 0 4 :=
  of_native_maps core2344 DegreeTwoThreeSpectrum4370.graph DegreeTwoThreeSpectrum4371.graph
    sourceMap2344 fusedMap2344 sourceMap2344_checked fusedMap2344_checked
    DegreeTwoThreeFiniteComparisons.comparison2344
#print axioms sourceMap2344_checked
#print axioms fusedMap2344_checked
#print axioms certified2344
def sourceMap2344swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2344swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2344swap_checked : acceptsGraphIso
    (source (graph core2344) (root 9) 4 0) DegreeTwoThreeSpectrum4370.graph sourceMap2344swap=true := by decide +kernel
theorem fusedMap2344swap_checked : acceptsGraphIso
    (fused (graph core2344) (root 9) 4 0) DegreeTwoThreeSpectrum4371.graph fusedMap2344swap=true := by decide +kernel
theorem certified2344swap : Certified (graph core2344) (root 9) 4 0 :=
  of_native_maps core2344 DegreeTwoThreeSpectrum4370.graph DegreeTwoThreeSpectrum4371.graph
    sourceMap2344swap fusedMap2344swap sourceMap2344swap_checked fusedMap2344swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2344
#print axioms sourceMap2344swap_checked
#print axioms fusedMap2344swap_checked
#print axioms certified2344swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
