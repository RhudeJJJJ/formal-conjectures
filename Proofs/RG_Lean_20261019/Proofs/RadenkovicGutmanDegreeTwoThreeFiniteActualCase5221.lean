/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5221 : Family 5 := level5.get ⟨7,by decide⟩
def sourceMap5221 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,9,6,7,8,0,10,11,12,13,14] (sourceLabel 5 2 5 v)
def fusedMap5221 : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (fusedLabel 5 2 5 v)
theorem sourceMap5221_checked : acceptsGraphIso
    (source (graph core5221) (root 5) 2 5) DegreeTwoThreeSpectrum2563.graph sourceMap5221=true := by decide +kernel
theorem fusedMap5221_checked : acceptsGraphIso
    (fused (graph core5221) (root 5) 2 5) DegreeTwoThreeSpectrum2333.graph fusedMap5221=true := by decide +kernel
theorem certified5221 : Certified (graph core5221) (root 5) 2 5 :=
  of_native_maps core5221 DegreeTwoThreeSpectrum2563.graph DegreeTwoThreeSpectrum2333.graph
    sourceMap5221 fusedMap5221 sourceMap5221_checked fusedMap5221_checked
    DegreeTwoThreeFiniteComparisons.comparison5221
#print axioms sourceMap5221_checked
#print axioms fusedMap5221_checked
#print axioms certified5221
def sourceMap5221swap : (Vertices 5 ⊕ Fin 6 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,2,3,4,5,9,0,10,11,12,13,14,6,7,8] (sourceLabel 5 5 2 v)
def fusedMap5221swap : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (fusedLabel 5 5 2 v)
theorem sourceMap5221swap_checked : acceptsGraphIso
    (source (graph core5221) (root 5) 5 2) DegreeTwoThreeSpectrum2563.graph sourceMap5221swap=true := by decide +kernel
theorem fusedMap5221swap_checked : acceptsGraphIso
    (fused (graph core5221) (root 5) 5 2) DegreeTwoThreeSpectrum2333.graph fusedMap5221swap=true := by decide +kernel
theorem certified5221swap : Certified (graph core5221) (root 5) 5 2 :=
  of_native_maps core5221 DegreeTwoThreeSpectrum2563.graph DegreeTwoThreeSpectrum2333.graph
    sourceMap5221swap fusedMap5221swap sourceMap5221swap_checked fusedMap5221swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5221
#print axioms sourceMap5221swap_checked
#print axioms fusedMap5221swap_checked
#print axioms certified5221swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
