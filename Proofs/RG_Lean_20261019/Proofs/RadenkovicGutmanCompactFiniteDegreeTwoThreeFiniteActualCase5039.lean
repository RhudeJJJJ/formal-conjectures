/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5039 : Family 10 := level10.get ⟨1737,by decide⟩
def sourceMap5039 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap5039 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5039_checked : acceptsGraphIso
    (source (graph core5039) (root 10) 2 2) DegreeTwoThreeSpectrum7640.graph sourceMap5039=true := by decide +kernel
theorem fusedMap5039_checked : acceptsGraphIso
    (fused (graph core5039) (root 10) 2 2) DegreeTwoThreeSpectrum6580.graph fusedMap5039=true := by decide +kernel
theorem certified5039 : Certified (graph core5039) (root 10) 2 2 :=
  of_native_maps core5039 DegreeTwoThreeSpectrum7640.graph DegreeTwoThreeSpectrum6580.graph
    sourceMap5039 fusedMap5039 sourceMap5039_checked fusedMap5039_checked
    DegreeTwoThreeFiniteComparisons.comparison5039
#print axioms sourceMap5039_checked
#print axioms fusedMap5039_checked
#print axioms certified5039
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
