/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5378 : Family 5 := level5.get ⟨10,by decide⟩
def sourceMap5378 : (Vertices 5 ⊕ Fin 5 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,11,12,13,14,15,1,2,3,4,5,6,7,8,9,10] (sourceLabel 5 4 4 v)
def fusedMap5378 : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15] (fusedLabel 5 4 4 v)
theorem sourceMap5378_checked : acceptsGraphIso
    (source (graph core5378) (root 5) 4 4) DegreeTwoThreeSpectrum4660.graph sourceMap5378=true := by decide +kernel
theorem fusedMap5378_checked : acceptsGraphIso
    (fused (graph core5378) (root 5) 4 4) DegreeTwoThreeSpectrum3864.graph fusedMap5378=true := by decide +kernel
theorem certified5378 : Certified (graph core5378) (root 5) 4 4 :=
  of_native_maps core5378 DegreeTwoThreeSpectrum4660.graph DegreeTwoThreeSpectrum3864.graph
    sourceMap5378 fusedMap5378 sourceMap5378_checked fusedMap5378_checked
    DegreeTwoThreeFiniteComparisons.comparison5378
#print axioms sourceMap5378_checked
#print axioms fusedMap5378_checked
#print axioms certified5378
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
