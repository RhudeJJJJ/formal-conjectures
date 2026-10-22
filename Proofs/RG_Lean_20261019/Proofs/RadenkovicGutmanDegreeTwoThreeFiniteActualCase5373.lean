/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5373 : Family 4 := level4.get ⟨3,by decide⟩
def sourceMap5373 : (Vertices 4 ⊕ Fin 5 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,11,12,13,14,1,2,3,4,5,6,7,8,9,10] (sourceLabel 4 4 4 v)
def fusedMap5373 : (Vertices 4 ⊕ Fin 10) → Fin 15 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12,13,14] (fusedLabel 4 4 4 v)
theorem sourceMap5373_checked : acceptsGraphIso
    (source (graph core5373) (root 4) 4 4) DegreeTwoThreeSpectrum2994.graph sourceMap5373=true := by decide +kernel
theorem fusedMap5373_checked : acceptsGraphIso
    (fused (graph core5373) (root 4) 4 4) DegreeTwoThreeSpectrum2311.graph fusedMap5373=true := by decide +kernel
theorem certified5373 : Certified (graph core5373) (root 4) 4 4 :=
  of_native_maps core5373 DegreeTwoThreeSpectrum2994.graph DegreeTwoThreeSpectrum2311.graph
    sourceMap5373 fusedMap5373 sourceMap5373_checked fusedMap5373_checked
    DegreeTwoThreeFiniteComparisons.comparison5373
#print axioms sourceMap5373_checked
#print axioms fusedMap5373_checked
#print axioms certified5373
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
