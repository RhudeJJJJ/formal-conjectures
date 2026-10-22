/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2517 : Family 10 := level10.get ⟨270,by decide⟩
def sourceMap2517 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2517 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 0 4 v)
theorem sourceMap2517_checked : acceptsGraphIso
    (source (graph core2517) (root 10) 0 4) DegreeTwoThreeSpectrum5392.graph sourceMap2517=true := by decide +kernel
theorem fusedMap2517_checked : acceptsGraphIso
    (fused (graph core2517) (root 10) 0 4) DegreeTwoThreeSpectrum5394.graph fusedMap2517=true := by decide +kernel
theorem certified2517 : Certified (graph core2517) (root 10) 0 4 :=
  of_native_maps core2517 DegreeTwoThreeSpectrum5392.graph DegreeTwoThreeSpectrum5394.graph
    sourceMap2517 fusedMap2517 sourceMap2517_checked fusedMap2517_checked
    DegreeTwoThreeFiniteComparisons.comparison2517
#print axioms sourceMap2517_checked
#print axioms fusedMap2517_checked
#print axioms certified2517
def sourceMap2517swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2517swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 4 0 v)
theorem sourceMap2517swap_checked : acceptsGraphIso
    (source (graph core2517) (root 10) 4 0) DegreeTwoThreeSpectrum5392.graph sourceMap2517swap=true := by decide +kernel
theorem fusedMap2517swap_checked : acceptsGraphIso
    (fused (graph core2517) (root 10) 4 0) DegreeTwoThreeSpectrum5394.graph fusedMap2517swap=true := by decide +kernel
theorem certified2517swap : Certified (graph core2517) (root 10) 4 0 :=
  of_native_maps core2517 DegreeTwoThreeSpectrum5392.graph DegreeTwoThreeSpectrum5394.graph
    sourceMap2517swap fusedMap2517swap sourceMap2517swap_checked fusedMap2517swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2517
#print axioms sourceMap2517swap_checked
#print axioms fusedMap2517swap_checked
#print axioms certified2517swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
