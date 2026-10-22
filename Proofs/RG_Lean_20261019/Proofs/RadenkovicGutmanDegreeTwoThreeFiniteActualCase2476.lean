/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2476 : Family 10 := level10.get ⟨117,by decide⟩
def sourceMap2476 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2476 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (fusedLabel 10 0 4 v)
theorem sourceMap2476_checked : acceptsGraphIso
    (source (graph core2476) (root 10) 0 4) DegreeTwoThreeSpectrum5650.graph sourceMap2476=true := by decide +kernel
theorem fusedMap2476_checked : acceptsGraphIso
    (fused (graph core2476) (root 10) 0 4) DegreeTwoThreeSpectrum5044.graph fusedMap2476=true := by decide +kernel
theorem certified2476 : Certified (graph core2476) (root 10) 0 4 :=
  of_native_maps core2476 DegreeTwoThreeSpectrum5650.graph DegreeTwoThreeSpectrum5044.graph
    sourceMap2476 fusedMap2476 sourceMap2476_checked fusedMap2476_checked
    DegreeTwoThreeFiniteComparisons.comparison2476
#print axioms sourceMap2476_checked
#print axioms fusedMap2476_checked
#print axioms certified2476
def sourceMap2476swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2476swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (fusedLabel 10 4 0 v)
theorem sourceMap2476swap_checked : acceptsGraphIso
    (source (graph core2476) (root 10) 4 0) DegreeTwoThreeSpectrum5650.graph sourceMap2476swap=true := by decide +kernel
theorem fusedMap2476swap_checked : acceptsGraphIso
    (fused (graph core2476) (root 10) 4 0) DegreeTwoThreeSpectrum5044.graph fusedMap2476swap=true := by decide +kernel
theorem certified2476swap : Certified (graph core2476) (root 10) 4 0 :=
  of_native_maps core2476 DegreeTwoThreeSpectrum5650.graph DegreeTwoThreeSpectrum5044.graph
    sourceMap2476swap fusedMap2476swap sourceMap2476swap_checked fusedMap2476swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2476
#print axioms sourceMap2476swap_checked
#print axioms fusedMap2476swap_checked
#print axioms certified2476swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
