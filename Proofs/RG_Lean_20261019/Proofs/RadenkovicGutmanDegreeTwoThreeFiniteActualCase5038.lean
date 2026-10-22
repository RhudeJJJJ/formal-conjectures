/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5038 : Family 10 := level10.get ⟨1729,by decide⟩
def sourceMap5038 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,12,13,14,15,16,6,7,8,9,10,11] (sourceLabel 10 2 2 v)
def fusedMap5038 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5038_checked : acceptsGraphIso
    (source (graph core5038) (root 10) 2 2) DegreeTwoThreeSpectrum7639.graph sourceMap5038=true := by decide +kernel
theorem fusedMap5038_checked : acceptsGraphIso
    (fused (graph core5038) (root 10) 2 2) DegreeTwoThreeSpectrum6534.graph fusedMap5038=true := by decide +kernel
theorem certified5038 : Certified (graph core5038) (root 10) 2 2 :=
  of_native_maps core5038 DegreeTwoThreeSpectrum7639.graph DegreeTwoThreeSpectrum6534.graph
    sourceMap5038 fusedMap5038 sourceMap5038_checked fusedMap5038_checked
    DegreeTwoThreeFiniteComparisons.comparison5038
#print axioms sourceMap5038_checked
#print axioms fusedMap5038_checked
#print axioms certified5038
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
