/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5048 : Family 10 := level10.get ⟨1785,by decide⟩
def sourceMap5048 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,10,11,12,13,14,15,16,4,5,6,7,8,9] (sourceLabel 10 2 2 v)
def fusedMap5048 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5048_checked : acceptsGraphIso
    (source (graph core5048) (root 10) 2 2) DegreeTwoThreeSpectrum7649.graph sourceMap5048=true := by decide +kernel
theorem fusedMap5048_checked : acceptsGraphIso
    (fused (graph core5048) (root 10) 2 2) DegreeTwoThreeSpectrum6865.graph fusedMap5048=true := by decide +kernel
theorem certified5048 : Certified (graph core5048) (root 10) 2 2 :=
  of_native_maps core5048 DegreeTwoThreeSpectrum7649.graph DegreeTwoThreeSpectrum6865.graph
    sourceMap5048 fusedMap5048 sourceMap5048_checked fusedMap5048_checked
    DegreeTwoThreeFiniteComparisons.comparison5048
#print axioms sourceMap5048_checked
#print axioms fusedMap5048_checked
#print axioms certified5048
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
