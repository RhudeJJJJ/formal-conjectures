/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons97
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4863 : Family 10 := level10.get ⟨1284,by decide⟩
def sourceMap4863 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4863 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4863_checked : acceptsGraphIso
    (source (graph core4863) (root 10) 2 2) DegreeTwoThreeSpectrum7366.graph sourceMap4863=true := by decide +kernel
theorem fusedMap4863_checked : acceptsGraphIso
    (fused (graph core4863) (root 10) 2 2) DegreeTwoThreeSpectrum6553.graph fusedMap4863=true := by decide +kernel
theorem certified4863 : Certified (graph core4863) (root 10) 2 2 :=
  of_native_maps core4863 DegreeTwoThreeSpectrum7366.graph DegreeTwoThreeSpectrum6553.graph
    sourceMap4863 fusedMap4863 sourceMap4863_checked fusedMap4863_checked
    DegreeTwoThreeFiniteComparisons.comparison4863
#print axioms sourceMap4863_checked
#print axioms fusedMap4863_checked
#print axioms certified4863
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
