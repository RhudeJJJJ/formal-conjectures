/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons96
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4811 : Family 10 := level10.get ⟨1160,by decide⟩
def sourceMap4811 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4811 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4811_checked : acceptsGraphIso
    (source (graph core4811) (root 10) 2 2) DegreeTwoThreeSpectrum7243.graph sourceMap4811=true := by decide +kernel
theorem fusedMap4811_checked : acceptsGraphIso
    (fused (graph core4811) (root 10) 2 2) DegreeTwoThreeSpectrum6304.graph fusedMap4811=true := by decide +kernel
theorem certified4811 : Certified (graph core4811) (root 10) 2 2 :=
  of_native_maps core4811 DegreeTwoThreeSpectrum7243.graph DegreeTwoThreeSpectrum6304.graph
    sourceMap4811 fusedMap4811 sourceMap4811_checked fusedMap4811_checked
    DegreeTwoThreeFiniteComparisons.comparison4811
#print axioms sourceMap4811_checked
#print axioms fusedMap4811_checked
#print axioms certified4811
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
