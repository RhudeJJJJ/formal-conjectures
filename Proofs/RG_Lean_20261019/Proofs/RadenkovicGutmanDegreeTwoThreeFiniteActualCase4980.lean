/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons99
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4980 : Family 10 := level10.get ⟨1574,by decide⟩
def sourceMap4980 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4980 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4980_checked : acceptsGraphIso
    (source (graph core4980) (root 10) 2 2) DegreeTwoThreeSpectrum7581.graph sourceMap4980=true := by decide +kernel
theorem fusedMap4980_checked : acceptsGraphIso
    (fused (graph core4980) (root 10) 2 2) DegreeTwoThreeSpectrum6055.graph fusedMap4980=true := by decide +kernel
theorem certified4980 : Certified (graph core4980) (root 10) 2 2 :=
  of_native_maps core4980 DegreeTwoThreeSpectrum7581.graph DegreeTwoThreeSpectrum6055.graph
    sourceMap4980 fusedMap4980 sourceMap4980_checked fusedMap4980_checked
    DegreeTwoThreeFiniteComparisons.comparison4980
#print axioms sourceMap4980_checked
#print axioms fusedMap4980_checked
#print axioms certified4980
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
