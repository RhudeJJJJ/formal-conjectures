/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5014 : Family 10 := level10.get ⟨1651,by decide⟩
def sourceMap5014 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap5014 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5014_checked : acceptsGraphIso
    (source (graph core5014) (root 10) 2 2) DegreeTwoThreeSpectrum7615.graph sourceMap5014=true := by decide +kernel
theorem fusedMap5014_checked : acceptsGraphIso
    (fused (graph core5014) (root 10) 2 2) DegreeTwoThreeSpectrum6244.graph fusedMap5014=true := by decide +kernel
theorem certified5014 : Certified (graph core5014) (root 10) 2 2 :=
  of_native_maps core5014 DegreeTwoThreeSpectrum7615.graph DegreeTwoThreeSpectrum6244.graph
    sourceMap5014 fusedMap5014 sourceMap5014_checked fusedMap5014_checked
    DegreeTwoThreeFiniteComparisons.comparison5014
#print axioms sourceMap5014_checked
#print axioms fusedMap5014_checked
#print axioms certified5014
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
