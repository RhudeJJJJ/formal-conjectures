/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5015 : Family 10 := level10.get ⟨1654,by decide⟩
def sourceMap5015 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap5015 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5015_checked : acceptsGraphIso
    (source (graph core5015) (root 10) 2 2) DegreeTwoThreeSpectrum7616.graph sourceMap5015=true := by decide +kernel
theorem fusedMap5015_checked : acceptsGraphIso
    (fused (graph core5015) (root 10) 2 2) DegreeTwoThreeSpectrum6254.graph fusedMap5015=true := by decide +kernel
theorem certified5015 : Certified (graph core5015) (root 10) 2 2 :=
  of_native_maps core5015 DegreeTwoThreeSpectrum7616.graph DegreeTwoThreeSpectrum6254.graph
    sourceMap5015 fusedMap5015 sourceMap5015_checked fusedMap5015_checked
    DegreeTwoThreeFiniteComparisons.comparison5015
#print axioms sourceMap5015_checked
#print axioms fusedMap5015_checked
#print axioms certified5015
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
