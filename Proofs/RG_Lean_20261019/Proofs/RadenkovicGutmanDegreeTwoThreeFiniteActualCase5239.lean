/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5239 : Family 6 := level6.get ⟨38,by decide⟩
def sourceMap5239 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,5,6,7,8,9,10,2,3,4,0,11,12,13,14,15] (sourceLabel 6 2 5 v)
def fusedMap5239 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 2 5 v)
theorem sourceMap5239_checked : acceptsGraphIso
    (source (graph core5239) (root 6) 2 5) DegreeTwoThreeSpectrum4563.graph sourceMap5239=true := by decide +kernel
theorem fusedMap5239_checked : acceptsGraphIso
    (fused (graph core5239) (root 6) 2 5) DegreeTwoThreeSpectrum3893.graph fusedMap5239=true := by decide +kernel
theorem certified5239 : Certified (graph core5239) (root 6) 2 5 :=
  of_native_maps core5239 DegreeTwoThreeSpectrum4563.graph DegreeTwoThreeSpectrum3893.graph
    sourceMap5239 fusedMap5239 sourceMap5239_checked fusedMap5239_checked
    DegreeTwoThreeFiniteComparisons.comparison5239
#print axioms sourceMap5239_checked
#print axioms fusedMap5239_checked
#print axioms certified5239
def sourceMap5239swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,5,6,7,8,9,10,0,11,12,13,14,15,2,3,4] (sourceLabel 6 5 2 v)
def fusedMap5239swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 5 2 v)
theorem sourceMap5239swap_checked : acceptsGraphIso
    (source (graph core5239) (root 6) 5 2) DegreeTwoThreeSpectrum4563.graph sourceMap5239swap=true := by decide +kernel
theorem fusedMap5239swap_checked : acceptsGraphIso
    (fused (graph core5239) (root 6) 5 2) DegreeTwoThreeSpectrum3893.graph fusedMap5239swap=true := by decide +kernel
theorem certified5239swap : Certified (graph core5239) (root 6) 5 2 :=
  of_native_maps core5239 DegreeTwoThreeSpectrum4563.graph DegreeTwoThreeSpectrum3893.graph
    sourceMap5239swap fusedMap5239swap sourceMap5239swap_checked fusedMap5239swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5239
#print axioms sourceMap5239swap_checked
#print axioms fusedMap5239swap_checked
#print axioms certified5239swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
