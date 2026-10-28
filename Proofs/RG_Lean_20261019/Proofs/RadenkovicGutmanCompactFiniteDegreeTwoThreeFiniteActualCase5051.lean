/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5051 : Family 10 := level10.get ⟨1804,by decide⟩
def sourceMap5051 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,7,8,9,10,11,12,13,14,15,16,1,2,3,4,5,6] (sourceLabel 10 2 2 v)
def fusedMap5051 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,12,1,0,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5051_checked : acceptsGraphIso
    (source (graph core5051) (root 10) 2 2) DegreeTwoThreeSpectrum7652.graph sourceMap5051=true := by decide +kernel
theorem fusedMap5051_checked : acceptsGraphIso
    (fused (graph core5051) (root 10) 2 2) DegreeTwoThreeSpectrum7064.graph fusedMap5051=true := by decide +kernel
theorem certified5051 : Certified (graph core5051) (root 10) 2 2 :=
  of_native_maps core5051 DegreeTwoThreeSpectrum7652.graph DegreeTwoThreeSpectrum7064.graph
    sourceMap5051 fusedMap5051 sourceMap5051_checked fusedMap5051_checked
    DegreeTwoThreeFiniteComparisons.comparison5051
#print axioms sourceMap5051_checked
#print axioms fusedMap5051_checked
#print axioms certified5051
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
