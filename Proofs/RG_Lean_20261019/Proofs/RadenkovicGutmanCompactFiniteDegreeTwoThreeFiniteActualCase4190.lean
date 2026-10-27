/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4190 : Family 8 := level8.get ⟨266,by decide⟩
def sourceMap4190 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,7,8,9,10,11,12,13,14,1,2,3,4,5,6] (sourceLabel 8 2 2 v)
def fusedMap4190 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4190_checked : acceptsGraphIso
    (source (graph core4190) (root 8) 2 2) DegreeTwoThreeSpectrum3851.graph sourceMap4190=true := by decide +kernel
theorem fusedMap4190_checked : acceptsGraphIso
    (fused (graph core4190) (root 8) 2 2) DegreeTwoThreeSpectrum3006.graph fusedMap4190=true := by decide +kernel
theorem certified4190 : Certified (graph core4190) (root 8) 2 2 :=
  of_native_maps core4190 DegreeTwoThreeSpectrum3851.graph DegreeTwoThreeSpectrum3006.graph
    sourceMap4190 fusedMap4190 sourceMap4190_checked fusedMap4190_checked
    DegreeTwoThreeFiniteComparisons.comparison4190
#print axioms sourceMap4190_checked
#print axioms fusedMap4190_checked
#print axioms certified4190
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
