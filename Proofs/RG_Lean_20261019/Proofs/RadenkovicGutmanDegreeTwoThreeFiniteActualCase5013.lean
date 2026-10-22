/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5013 : Family 10 := level10.get ⟨1650,by decide⟩
def sourceMap5013 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap5013 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5013_checked : acceptsGraphIso
    (source (graph core5013) (root 10) 2 2) DegreeTwoThreeSpectrum7614.graph sourceMap5013=true := by decide +kernel
theorem fusedMap5013_checked : acceptsGraphIso
    (fused (graph core5013) (root 10) 2 2) DegreeTwoThreeSpectrum6243.graph fusedMap5013=true := by decide +kernel
theorem certified5013 : Certified (graph core5013) (root 10) 2 2 :=
  of_native_maps core5013 DegreeTwoThreeSpectrum7614.graph DegreeTwoThreeSpectrum6243.graph
    sourceMap5013 fusedMap5013 sourceMap5013_checked fusedMap5013_checked
    DegreeTwoThreeFiniteComparisons.comparison5013
#print axioms sourceMap5013_checked
#print axioms fusedMap5013_checked
#print axioms certified5013
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
