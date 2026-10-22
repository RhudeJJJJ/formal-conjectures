/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons91
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4574 : Family 10 := level10.get ⟨520,by decide⟩
def sourceMap4574 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4574 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4574_checked : acceptsGraphIso
    (source (graph core4574) (root 10) 2 2) DegreeTwoThreeSpectrum7121.graph sourceMap4574=true := by decide +kernel
theorem fusedMap4574_checked : acceptsGraphIso
    (fused (graph core4574) (root 10) 2 2) DegreeTwoThreeSpectrum5163.graph fusedMap4574=true := by decide +kernel
theorem certified4574 : Certified (graph core4574) (root 10) 2 2 :=
  of_native_maps core4574 DegreeTwoThreeSpectrum7121.graph DegreeTwoThreeSpectrum5163.graph
    sourceMap4574 fusedMap4574 sourceMap4574_checked fusedMap4574_checked
    DegreeTwoThreeFiniteComparisons.comparison4574
#print axioms sourceMap4574_checked
#print axioms fusedMap4574_checked
#print axioms certified4574
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
