/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5053 : Family 10 := level10.get ⟨1812,by decide⟩
def sourceMap5053 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,7,8,9,10,11,12,13,14,15,16,1,2,3,4,5,6] (sourceLabel 10 2 2 v)
def fusedMap5053 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,12,1,0,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5053_checked : acceptsGraphIso
    (source (graph core5053) (root 10) 2 2) DegreeTwoThreeSpectrum7654.graph sourceMap5053=true := by decide +kernel
theorem fusedMap5053_checked : acceptsGraphIso
    (fused (graph core5053) (root 10) 2 2) DegreeTwoThreeSpectrum7082.graph fusedMap5053=true := by decide +kernel
theorem certified5053 : Certified (graph core5053) (root 10) 2 2 :=
  of_native_maps core5053 DegreeTwoThreeSpectrum7654.graph DegreeTwoThreeSpectrum7082.graph
    sourceMap5053 fusedMap5053 sourceMap5053_checked fusedMap5053_checked
    DegreeTwoThreeFiniteComparisons.comparison5053
#print axioms sourceMap5053_checked
#print axioms fusedMap5053_checked
#print axioms certified5053
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
