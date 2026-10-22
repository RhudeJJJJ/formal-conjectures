/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5047 : Family 10 := level10.get ⟨1768,by decide⟩
def sourceMap5047 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,11,12,13,14,15,16,5,6,7,8,9,10] (sourceLabel 10 2 2 v)
def fusedMap5047 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5047_checked : acceptsGraphIso
    (source (graph core5047) (root 10) 2 2) DegreeTwoThreeSpectrum7648.graph sourceMap5047=true := by decide +kernel
theorem fusedMap5047_checked : acceptsGraphIso
    (fused (graph core5047) (root 10) 2 2) DegreeTwoThreeSpectrum6685.graph fusedMap5047=true := by decide +kernel
theorem certified5047 : Certified (graph core5047) (root 10) 2 2 :=
  of_native_maps core5047 DegreeTwoThreeSpectrum7648.graph DegreeTwoThreeSpectrum6685.graph
    sourceMap5047 fusedMap5047 sourceMap5047_checked fusedMap5047_checked
    DegreeTwoThreeFiniteComparisons.comparison5047
#print axioms sourceMap5047_checked
#print axioms fusedMap5047_checked
#print axioms certified5047
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
