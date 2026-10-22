/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4103 : Family 8 := level8.get ⟨32,by decide⟩
def sourceMap4103 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,8,9,2,3,4,5,6,7] (sourceLabel 8 2 2 v)
def fusedMap4103 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,13,14,7,8,9,10,11,12] (fusedLabel 8 2 2 v)
theorem sourceMap4103_checked : acceptsGraphIso
    (source (graph core4103) (root 8) 2 2) DegreeTwoThreeSpectrum2815.graph sourceMap4103=true := by decide +kernel
theorem fusedMap4103_checked : acceptsGraphIso
    (fused (graph core4103) (root 8) 2 2) DegreeTwoThreeSpectrum2435.graph fusedMap4103=true := by decide +kernel
theorem certified4103 : Certified (graph core4103) (root 8) 2 2 :=
  of_native_maps core4103 DegreeTwoThreeSpectrum2815.graph DegreeTwoThreeSpectrum2435.graph
    sourceMap4103 fusedMap4103 sourceMap4103_checked fusedMap4103_checked
    DegreeTwoThreeFiniteComparisons.comparison4103
#print axioms sourceMap4103_checked
#print axioms fusedMap4103_checked
#print axioms certified4103
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
