/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4627 : Family 10 := level10.get ⟨674,by decide⟩
def sourceMap4627 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4627 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4627_checked : acceptsGraphIso
    (source (graph core4627) (root 10) 2 2) DegreeTwoThreeSpectrum6462.graph sourceMap4627=true := by decide +kernel
theorem fusedMap4627_checked : acceptsGraphIso
    (fused (graph core4627) (root 10) 2 2) DegreeTwoThreeSpectrum5396.graph fusedMap4627=true := by decide +kernel
theorem certified4627 : Certified (graph core4627) (root 10) 2 2 :=
  of_native_maps core4627 DegreeTwoThreeSpectrum6462.graph DegreeTwoThreeSpectrum5396.graph
    sourceMap4627 fusedMap4627 sourceMap4627_checked fusedMap4627_checked
    DegreeTwoThreeFiniteComparisons.comparison4627
#print axioms sourceMap4627_checked
#print axioms fusedMap4627_checked
#print axioms certified4627
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
