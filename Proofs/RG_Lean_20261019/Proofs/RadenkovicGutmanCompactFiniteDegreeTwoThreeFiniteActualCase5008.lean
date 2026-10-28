/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5008 : Family 10 := level10.get ⟨1638,by decide⟩
def sourceMap5008 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap5008 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5008_checked : acceptsGraphIso
    (source (graph core5008) (root 10) 2 2) DegreeTwoThreeSpectrum7609.graph sourceMap5008=true := by decide +kernel
theorem fusedMap5008_checked : acceptsGraphIso
    (fused (graph core5008) (root 10) 2 2) DegreeTwoThreeSpectrum6213.graph fusedMap5008=true := by decide +kernel
theorem certified5008 : Certified (graph core5008) (root 10) 2 2 :=
  of_native_maps core5008 DegreeTwoThreeSpectrum7609.graph DegreeTwoThreeSpectrum6213.graph
    sourceMap5008 fusedMap5008 sourceMap5008_checked fusedMap5008_checked
    DegreeTwoThreeFiniteComparisons.comparison5008
#print axioms sourceMap5008_checked
#print axioms fusedMap5008_checked
#print axioms certified5008
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
