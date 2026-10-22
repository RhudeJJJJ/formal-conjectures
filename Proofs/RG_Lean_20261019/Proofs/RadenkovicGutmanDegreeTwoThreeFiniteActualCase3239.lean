/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3239 : Family 9 := level9.get ⟨28,by decide⟩
def sourceMap3239 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 9 0 5 v)
def fusedMap3239 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,16,9,10,11,12,13,14,15] (fusedLabel 9 0 5 v)
theorem sourceMap3239_checked : acceptsGraphIso
    (source (graph core3239) (root 9) 0 5) DegreeTwoThreeSpectrum5078.graph sourceMap3239=true := by decide +kernel
theorem fusedMap3239_checked : acceptsGraphIso
    (fused (graph core3239) (root 9) 0 5) DegreeTwoThreeSpectrum5080.graph fusedMap3239=true := by decide +kernel
theorem certified3239 : Certified (graph core3239) (root 9) 0 5 :=
  of_native_maps core3239 DegreeTwoThreeSpectrum5078.graph DegreeTwoThreeSpectrum5080.graph
    sourceMap3239 fusedMap3239 sourceMap3239_checked fusedMap3239_checked
    DegreeTwoThreeFiniteComparisons.comparison3239
#print axioms sourceMap3239_checked
#print axioms fusedMap3239_checked
#print axioms certified3239
def sourceMap3239swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14,16] (sourceLabel 9 5 0 v)
def fusedMap3239swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,16,9,10,11,12,13,14,15] (fusedLabel 9 5 0 v)
theorem sourceMap3239swap_checked : acceptsGraphIso
    (source (graph core3239) (root 9) 5 0) DegreeTwoThreeSpectrum5078.graph sourceMap3239swap=true := by decide +kernel
theorem fusedMap3239swap_checked : acceptsGraphIso
    (fused (graph core3239) (root 9) 5 0) DegreeTwoThreeSpectrum5080.graph fusedMap3239swap=true := by decide +kernel
theorem certified3239swap : Certified (graph core3239) (root 9) 5 0 :=
  of_native_maps core3239 DegreeTwoThreeSpectrum5078.graph DegreeTwoThreeSpectrum5080.graph
    sourceMap3239swap fusedMap3239swap sourceMap3239swap_checked fusedMap3239swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3239
#print axioms sourceMap3239swap_checked
#print axioms fusedMap3239swap_checked
#print axioms certified3239swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
