/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2239 : Family 9 := level9.get ⟨110,by decide⟩
def sourceMap2239 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,15,8,9,10,11,12] (sourceLabel 9 0 4 v)
def fusedMap2239 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,8,9,10,11,12,13] (fusedLabel 9 0 4 v)
theorem sourceMap2239_checked : acceptsGraphIso
    (source (graph core2239) (root 9) 0 4) DegreeTwoThreeSpectrum4111.graph sourceMap2239=true := by decide +kernel
theorem fusedMap2239_checked : acceptsGraphIso
    (fused (graph core2239) (root 9) 0 4) DegreeTwoThreeSpectrum4113.graph fusedMap2239=true := by decide +kernel
theorem certified2239 : Certified (graph core2239) (root 9) 0 4 :=
  of_native_maps core2239 DegreeTwoThreeSpectrum4111.graph DegreeTwoThreeSpectrum4113.graph
    sourceMap2239 fusedMap2239 sourceMap2239_checked fusedMap2239_checked
    DegreeTwoThreeFiniteComparisons.comparison2239
#print axioms sourceMap2239_checked
#print axioms fusedMap2239_checked
#print axioms certified2239
def sourceMap2239swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,8,9,10,11,12,15] (sourceLabel 9 4 0 v)
def fusedMap2239swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,8,9,10,11,12,13] (fusedLabel 9 4 0 v)
theorem sourceMap2239swap_checked : acceptsGraphIso
    (source (graph core2239) (root 9) 4 0) DegreeTwoThreeSpectrum4111.graph sourceMap2239swap=true := by decide +kernel
theorem fusedMap2239swap_checked : acceptsGraphIso
    (fused (graph core2239) (root 9) 4 0) DegreeTwoThreeSpectrum4113.graph fusedMap2239swap=true := by decide +kernel
theorem certified2239swap : Certified (graph core2239) (root 9) 4 0 :=
  of_native_maps core2239 DegreeTwoThreeSpectrum4111.graph DegreeTwoThreeSpectrum4113.graph
    sourceMap2239swap fusedMap2239swap sourceMap2239swap_checked fusedMap2239swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2239
#print axioms sourceMap2239swap_checked
#print axioms fusedMap2239swap_checked
#print axioms certified2239swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
