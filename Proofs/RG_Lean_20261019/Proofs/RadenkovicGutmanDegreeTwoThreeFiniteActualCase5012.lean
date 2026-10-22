/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5012 : Family 10 := level10.get ⟨1648,by decide⟩
def sourceMap5012 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap5012 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5012_checked : acceptsGraphIso
    (source (graph core5012) (root 10) 2 2) DegreeTwoThreeSpectrum7613.graph sourceMap5012=true := by decide +kernel
theorem fusedMap5012_checked : acceptsGraphIso
    (fused (graph core5012) (root 10) 2 2) DegreeTwoThreeSpectrum6238.graph fusedMap5012=true := by decide +kernel
theorem certified5012 : Certified (graph core5012) (root 10) 2 2 :=
  of_native_maps core5012 DegreeTwoThreeSpectrum7613.graph DegreeTwoThreeSpectrum6238.graph
    sourceMap5012 fusedMap5012 sourceMap5012_checked fusedMap5012_checked
    DegreeTwoThreeFiniteComparisons.comparison5012
#print axioms sourceMap5012_checked
#print axioms fusedMap5012_checked
#print axioms certified5012
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
