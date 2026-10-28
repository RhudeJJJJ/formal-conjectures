/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5016 : Family 10 := level10.get ⟨1655,by decide⟩
def sourceMap5016 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap5016 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5016_checked : acceptsGraphIso
    (source (graph core5016) (root 10) 2 2) DegreeTwoThreeSpectrum7617.graph sourceMap5016=true := by decide +kernel
theorem fusedMap5016_checked : acceptsGraphIso
    (fused (graph core5016) (root 10) 2 2) DegreeTwoThreeSpectrum6255.graph fusedMap5016=true := by decide +kernel
theorem certified5016 : Certified (graph core5016) (root 10) 2 2 :=
  of_native_maps core5016 DegreeTwoThreeSpectrum7617.graph DegreeTwoThreeSpectrum6255.graph
    sourceMap5016 fusedMap5016 sourceMap5016_checked fusedMap5016_checked
    DegreeTwoThreeFiniteComparisons.comparison5016
#print axioms sourceMap5016_checked
#print axioms fusedMap5016_checked
#print axioms certified5016
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
