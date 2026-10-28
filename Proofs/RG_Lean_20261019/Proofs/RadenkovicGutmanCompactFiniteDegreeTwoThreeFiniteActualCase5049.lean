/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5049 : Family 10 := level10.get ⟨1801,by decide⟩
def sourceMap5049 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,7,8,9,10,11,12,13,14,15,16,1,2,3,4,5,6] (sourceLabel 10 2 2 v)
def fusedMap5049 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,12,1,0,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5049_checked : acceptsGraphIso
    (source (graph core5049) (root 10) 2 2) DegreeTwoThreeSpectrum7650.graph sourceMap5049=true := by decide +kernel
theorem fusedMap5049_checked : acceptsGraphIso
    (fused (graph core5049) (root 10) 2 2) DegreeTwoThreeSpectrum7058.graph fusedMap5049=true := by decide +kernel
theorem certified5049 : Certified (graph core5049) (root 10) 2 2 :=
  of_native_maps core5049 DegreeTwoThreeSpectrum7650.graph DegreeTwoThreeSpectrum7058.graph
    sourceMap5049 fusedMap5049 sourceMap5049_checked fusedMap5049_checked
    DegreeTwoThreeFiniteComparisons.comparison5049
#print axioms sourceMap5049_checked
#print axioms fusedMap5049_checked
#print axioms certified5049
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
