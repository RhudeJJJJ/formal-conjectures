/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4623 : Family 10 := level10.get ⟨667,by decide⟩
def sourceMap4623 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,14,15,16,13,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap4623 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4623_checked : acceptsGraphIso
    (source (graph core4623) (root 10) 2 2) DegreeTwoThreeSpectrum7320.graph sourceMap4623=true := by decide +kernel
theorem fusedMap4623_checked : acceptsGraphIso
    (fused (graph core4623) (root 10) 2 2) DegreeTwoThreeSpectrum5379.graph fusedMap4623=true := by decide +kernel
theorem certified4623 : Certified (graph core4623) (root 10) 2 2 :=
  of_native_maps core4623 DegreeTwoThreeSpectrum7320.graph DegreeTwoThreeSpectrum5379.graph
    sourceMap4623 fusedMap4623 sourceMap4623_checked fusedMap4623_checked
    DegreeTwoThreeFiniteComparisons.comparison4623
#print axioms sourceMap4623_checked
#print axioms fusedMap4623_checked
#print axioms certified4623
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
