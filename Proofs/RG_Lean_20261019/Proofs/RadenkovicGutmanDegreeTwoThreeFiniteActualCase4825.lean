/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons96
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4825 : Family 10 := level10.get ⟨1195,by decide⟩
def sourceMap4825 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4825 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4825_checked : acceptsGraphIso
    (source (graph core4825) (root 10) 2 2) DegreeTwoThreeSpectrum7283.graph sourceMap4825=true := by decide +kernel
theorem fusedMap4825_checked : acceptsGraphIso
    (fused (graph core4825) (root 10) 2 2) DegreeTwoThreeSpectrum6369.graph fusedMap4825=true := by decide +kernel
theorem certified4825 : Certified (graph core4825) (root 10) 2 2 :=
  of_native_maps core4825 DegreeTwoThreeSpectrum7283.graph DegreeTwoThreeSpectrum6369.graph
    sourceMap4825 fusedMap4825 sourceMap4825_checked fusedMap4825_checked
    DegreeTwoThreeFiniteComparisons.comparison4825
#print axioms sourceMap4825_checked
#print axioms fusedMap4825_checked
#print axioms certified4825
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
