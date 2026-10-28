/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5035 : Family 10 := level10.get ⟨1719,by decide⟩
def sourceMap5035 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,13,14,15,16,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap5035 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5035_checked : acceptsGraphIso
    (source (graph core5035) (root 10) 2 2) DegreeTwoThreeSpectrum7636.graph sourceMap5035=true := by decide +kernel
theorem fusedMap5035_checked : acceptsGraphIso
    (fused (graph core5035) (root 10) 2 2) DegreeTwoThreeSpectrum6506.graph fusedMap5035=true := by decide +kernel
theorem certified5035 : Certified (graph core5035) (root 10) 2 2 :=
  of_native_maps core5035 DegreeTwoThreeSpectrum7636.graph DegreeTwoThreeSpectrum6506.graph
    sourceMap5035 fusedMap5035 sourceMap5035_checked fusedMap5035_checked
    DegreeTwoThreeFiniteComparisons.comparison5035
#print axioms sourceMap5035_checked
#print axioms fusedMap5035_checked
#print axioms certified5035
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
