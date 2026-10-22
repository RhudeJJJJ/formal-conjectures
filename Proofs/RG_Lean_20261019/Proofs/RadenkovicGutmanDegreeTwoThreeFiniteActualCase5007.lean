/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5007 : Family 10 := level10.get ⟨1635,by decide⟩
def sourceMap5007 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap5007 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5007_checked : acceptsGraphIso
    (source (graph core5007) (root 10) 2 2) DegreeTwoThreeSpectrum7608.graph sourceMap5007=true := by decide +kernel
theorem fusedMap5007_checked : acceptsGraphIso
    (fused (graph core5007) (root 10) 2 2) DegreeTwoThreeSpectrum6203.graph fusedMap5007=true := by decide +kernel
theorem certified5007 : Certified (graph core5007) (root 10) 2 2 :=
  of_native_maps core5007 DegreeTwoThreeSpectrum7608.graph DegreeTwoThreeSpectrum6203.graph
    sourceMap5007 fusedMap5007 sourceMap5007_checked fusedMap5007_checked
    DegreeTwoThreeFiniteComparisons.comparison5007
#print axioms sourceMap5007_checked
#print axioms fusedMap5007_checked
#print axioms certified5007
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
