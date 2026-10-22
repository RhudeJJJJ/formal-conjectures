/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5029 : Family 10 := level10.get ⟨1706,by decide⟩
def sourceMap5029 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap5029 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5029_checked : acceptsGraphIso
    (source (graph core5029) (root 10) 2 2) DegreeTwoThreeSpectrum7630.graph sourceMap5029=true := by decide +kernel
theorem fusedMap5029_checked : acceptsGraphIso
    (fused (graph core5029) (root 10) 2 2) DegreeTwoThreeSpectrum6476.graph fusedMap5029=true := by decide +kernel
theorem certified5029 : Certified (graph core5029) (root 10) 2 2 :=
  of_native_maps core5029 DegreeTwoThreeSpectrum7630.graph DegreeTwoThreeSpectrum6476.graph
    sourceMap5029 fusedMap5029 sourceMap5029_checked fusedMap5029_checked
    DegreeTwoThreeFiniteComparisons.comparison5029
#print axioms sourceMap5029_checked
#print axioms fusedMap5029_checked
#print axioms certified5029
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
