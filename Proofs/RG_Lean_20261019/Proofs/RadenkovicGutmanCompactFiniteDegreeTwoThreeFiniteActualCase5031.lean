/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5031 : Family 10 := level10.get ⟨1711,by decide⟩
def sourceMap5031 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap5031 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5031_checked : acceptsGraphIso
    (source (graph core5031) (root 10) 2 2) DegreeTwoThreeSpectrum7632.graph sourceMap5031=true := by decide +kernel
theorem fusedMap5031_checked : acceptsGraphIso
    (fused (graph core5031) (root 10) 2 2) DegreeTwoThreeSpectrum6487.graph fusedMap5031=true := by decide +kernel
theorem certified5031 : Certified (graph core5031) (root 10) 2 2 :=
  of_native_maps core5031 DegreeTwoThreeSpectrum7632.graph DegreeTwoThreeSpectrum6487.graph
    sourceMap5031 fusedMap5031 sourceMap5031_checked fusedMap5031_checked
    DegreeTwoThreeFiniteComparisons.comparison5031
#print axioms sourceMap5031_checked
#print axioms fusedMap5031_checked
#print axioms certified5031
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
