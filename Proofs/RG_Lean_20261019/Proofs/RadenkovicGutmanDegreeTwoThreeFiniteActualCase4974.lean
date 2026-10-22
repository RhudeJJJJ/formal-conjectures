/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons99
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4974 : Family 10 := level10.get ⟨1558,by decide⟩
def sourceMap4974 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4974 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4974_checked : acceptsGraphIso
    (source (graph core4974) (root 10) 2 2) DegreeTwoThreeSpectrum7575.graph sourceMap4974=true := by decide +kernel
theorem fusedMap4974_checked : acceptsGraphIso
    (fused (graph core4974) (root 10) 2 2) DegreeTwoThreeSpectrum6021.graph fusedMap4974=true := by decide +kernel
theorem certified4974 : Certified (graph core4974) (root 10) 2 2 :=
  of_native_maps core4974 DegreeTwoThreeSpectrum7575.graph DegreeTwoThreeSpectrum6021.graph
    sourceMap4974 fusedMap4974 sourceMap4974_checked fusedMap4974_checked
    DegreeTwoThreeFiniteComparisons.comparison4974
#print axioms sourceMap4974_checked
#print axioms fusedMap4974_checked
#print axioms certified4974
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
