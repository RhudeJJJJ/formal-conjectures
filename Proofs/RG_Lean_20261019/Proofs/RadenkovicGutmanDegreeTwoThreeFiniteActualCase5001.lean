/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5001 : Family 10 := level10.get ⟨1622,by decide⟩
def sourceMap5001 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap5001 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5001_checked : acceptsGraphIso
    (source (graph core5001) (root 10) 2 2) DegreeTwoThreeSpectrum7602.graph sourceMap5001=true := by decide +kernel
theorem fusedMap5001_checked : acceptsGraphIso
    (fused (graph core5001) (root 10) 2 2) DegreeTwoThreeSpectrum6180.graph fusedMap5001=true := by decide +kernel
theorem certified5001 : Certified (graph core5001) (root 10) 2 2 :=
  of_native_maps core5001 DegreeTwoThreeSpectrum7602.graph DegreeTwoThreeSpectrum6180.graph
    sourceMap5001 fusedMap5001 sourceMap5001_checked fusedMap5001_checked
    DegreeTwoThreeFiniteComparisons.comparison5001
#print axioms sourceMap5001_checked
#print axioms fusedMap5001_checked
#print axioms certified5001
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
