/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5040 : Family 10 := level10.get ⟨1738,by decide⟩
def sourceMap5040 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap5040 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5040_checked : acceptsGraphIso
    (source (graph core5040) (root 10) 2 2) DegreeTwoThreeSpectrum7641.graph sourceMap5040=true := by decide +kernel
theorem fusedMap5040_checked : acceptsGraphIso
    (fused (graph core5040) (root 10) 2 2) DegreeTwoThreeSpectrum6581.graph fusedMap5040=true := by decide +kernel
theorem certified5040 : Certified (graph core5040) (root 10) 2 2 :=
  of_native_maps core5040 DegreeTwoThreeSpectrum7641.graph DegreeTwoThreeSpectrum6581.graph
    sourceMap5040 fusedMap5040 sourceMap5040_checked fusedMap5040_checked
    DegreeTwoThreeFiniteComparisons.comparison5040
#print axioms sourceMap5040_checked
#print axioms fusedMap5040_checked
#print axioms certified5040
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
