/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons97
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4888 : Family 10 := level10.get ⟨1340,by decide⟩
def sourceMap4888 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,13,14,15,16,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap4888 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4888_checked : acceptsGraphIso
    (source (graph core4888) (root 10) 2 2) DegreeTwoThreeSpectrum7418.graph sourceMap4888=true := by decide +kernel
theorem fusedMap4888_checked : acceptsGraphIso
    (fused (graph core4888) (root 10) 2 2) DegreeTwoThreeSpectrum6662.graph fusedMap4888=true := by decide +kernel
theorem certified4888 : Certified (graph core4888) (root 10) 2 2 :=
  of_native_maps core4888 DegreeTwoThreeSpectrum7418.graph DegreeTwoThreeSpectrum6662.graph
    sourceMap4888 fusedMap4888 sourceMap4888_checked fusedMap4888_checked
    DegreeTwoThreeFiniteComparisons.comparison4888
#print axioms sourceMap4888_checked
#print axioms fusedMap4888_checked
#print axioms certified4888
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
